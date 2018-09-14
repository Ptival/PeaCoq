declare namespace AceAjax {
    export interface Anchor {
        $insertRight: boolean
    }
    export interface IEditSession {
        _signal(s: string): void
    }
    interface Completion {
        caption?: string
        meta: string
        score?: number
        snippet?: string
        value?: string
    }
    interface Completer {
        getCompletions: (editor: Editor, session: IEditSession, position: AceAjax.Position, prefix: string, callback: (err: boolean, results: Completion[]) => void) => void
    }
    export interface Editor {
        completer: any
        completers: Completer[]
    }
}

interface JQueryContextMenuBuildOptions {
    selector: string
    trigger?: string
    build: (trigger: JQuery, event: Event) => boolean | any
}

interface JQueryStatic {
    contextMenu(options: JQueryContextMenuBuildOptions): JQuery
}

declare var sexpParse: (o: any) => any

declare namespace W2UI {
    interface W2Tabs extends W2Common, W2OnClickable {
        owner: W2UI.W2Layout
    }
}

declare var jss : any

declare namespace Rx {
    interface Observable<T> extends IObservable<T> {
        filter<U extends T>(predicate: (value: T, index: number, source: Observable<T>) => value is U, thisArg?: any): Observable<U>
    }
}
