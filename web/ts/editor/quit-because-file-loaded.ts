import * as Command from "../sertop/command";
import * as ControlCommand from "../sertop/control-command";

export function setup(
  doc: ICoqDocument,
  loadedFile$: Rx.Observable<{}>
): void {
  loadedFile$
    .startWith({}) // quit upon loading the webpage
    .map(({}) => Rx.Observable.just(new Command.Control(new ControlCommand.Quit())))
    .subscribe(cmd$ => doc.sendCommands(cmd$));
}
