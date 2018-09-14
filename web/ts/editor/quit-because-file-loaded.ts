import { Quit } from "../sertop/serapi-protocol"

export function setup(
    doc : ICoqDocument,
    loadedFile$ : Rx.Observable<{}>
) : void {
    loadedFile$
        .startWith({}) // quit upon loading the webpage
        .map(({}) => Rx.Observable.just(new Quit()))
        .subscribe(cmd$ => doc.sendCommands(cmd$))
}
