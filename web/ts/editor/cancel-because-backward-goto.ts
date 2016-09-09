import * as Command from "../sertop/command";
import * as ControlCommand from "../sertop/control-command";

export function setup(
  doc: ICoqDocument,
  backwardGoTo$: Rx.Observable<AceAjax.Position>
): void {

  backwardGoTo$
    .flatMap(destinationPos => {
      const maybeSentence = doc.getSentenceAtPosition(destinationPos);
      return (
        maybeSentence
          .bind(e => e.getStateId())
          .fmap(s => new Command.Control(new ControlCommand.StmCancel([s])))
          .caseOf({
            nothing: () => [],
            just: cmd => [Rx.Observable.just(cmd)],
          })
      );
    })
    .subscribe(cmd$ => doc.sendCommands(cmd$));

}
