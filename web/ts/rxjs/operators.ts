/*
This achieves two things:
- events happen every `time` if some input has been received
- an event happens `time` after the last input
*/
export function debounceAndThrottle(time: number)
: (s: Rx.Observable<{}>) => Rx.Observable<{}> {
  return s => Rx.Observable.merge(s.debounce(time), s.throttle(time))
}
