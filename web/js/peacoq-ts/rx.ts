// I'm not sure whether there is a simpler way to do all this.

/*
`processSequentiallyUntilError` will process `input$` items with
`process` one by one, waiting for the output from the previous item
before processing the next one.
If
*/
function processSequentiallyUntilError<I, O>(
  input$: Rx.Observable<I>,
  process: (input$: Rx.Observable<I>) => Rx.Observable<O>
): Rx.Observable<O> {
  /*
  This stream yields the same items as `input$`, but only after the
  previous item has been `process`ed and its result showed up in
  `output$`.
  */
  const bufferedInputSubject = new Rx.Subject<I>();
  /*
  Note that `output$` will process items until one of them fails, at
  which point it will end with an error.
  `ready$` consumes `output$` and has to catch this error.
  */
  const output$ = process(bufferedInputSubject.asObservable()).share();
  /*
  This stream regulates the flow of `input$` into `bufferedInputSubject`.
  When `output$` errors, it gracefully terminates, preventing more
  processing for this round.
  */
  const ready$ = output$
    .map(o => ({})) // only interested in the presence of an output
    .startWith({}) // to get the process started, need an initial trigger
    .catch(_ => Rx.Observable.empty()) // when output errors, just complete
    .publish(); // stall so that zip does not miss the first ready
  /*
  `zip` effectively staggers `input$` until `ready$` outputs another item
  */
  Rx.Observable.zip(input$, ready$, (i, o) => i).subscribe(i => bufferedInputSubject.onNext(i));
  ready$.connect();
  return output$;
}

/*
This helper uses `processSequentiallyUntilError` to process `input$`
items one after the other until an error arises.
When an error arises, it relays it to the error observer, and resumes
the processing.
Note that, in the intended scenario, `input$` is a hot observable,
and this function will ignore all inputs that have been queued after
the failing input and before its failure.
That is, the process is resumed from the current state of the
observable.
*/
function processSequentiallyForeverRec<I, O, E>(
  input$: Rx.Observable<I>,
  process: (input$: Rx.Observable<I>) => Rx.Observable<O>,
  outputObserver: Rx.Observer<O>,
  errorObserver: Rx.Observer<E>
) {
  processSequentiallyUntilError<I, O>(input$, process).subscribe(
    o => outputObserver.onNext(o),
    e => {
      processSequentiallyForeverRec(input$, process, outputObserver, errorObserver);
      /*
      The error is raised after resuming the processing, so that the
      error handler can send input on `input$` without it being ignored.
      It seems like the input sent by the error observer is the first
      to show up, but this might not always be the case...
      */
      errorObserver.onNext(e);
    }
  );
}

interface OutputAndErrorStreams<O> {
  error$: Rx.Observable<any>;
  output$: Rx.Observable<O>;
}

/*
`processSequentiallyForever` processes `input$` sequentially until it
errors. Upon error, it yields the error on `error$` and resumes at
whatever state `input$` is currently (dropping the inputs that were
queued in the time between the failing input and its failure).
*/
export function processSequentiallyForever<I, O>(
  input$: Rx.Observable<I>,
  process: (input$: Rx.Observable<I>) => Rx.Observable<O>
): OutputAndErrorStreams<O> {
  let outputSubject = new Rx.Subject<O>();
  let errorSubject = new Rx.Subject<E>();
  let firstOutput = processSequentiallyForeverRec(input$, process, outputSubject.asObserver(), errorSubject.asObserver());
  return {
    error$: errorSubject.asObservable(),
    output$: outputSubject.asObservable(),
  };
}
