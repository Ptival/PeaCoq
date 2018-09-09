import * as _ from 'lodash'

export class Tab implements ITab {
    private _captionShouldBeBold : boolean
    private captionSuffix : string
    public div : JQuery
    // TODO : use Observables
    private onClickHandlers : Function[]
    private onResizeHandlers : Function[]
    private tab : W2UI.W2Tabs

    constructor(
        public id : string,
        public caption : string,
        layoutName : string,
        public panel : string
    ) {
        this.caption = caption
        this.captionSuffix = ''
        this.id = id
        this.panel = panel
        const w2uiId = layoutName + '_' + panel + '_tabs'
        this.tab = w2ui[w2uiId]

        const self = this

        this.div = $('<div>', { id : id + '-content', style : 'height : 100%', text : '' })
        this.onClickHandlers = []
        this.onResizeHandlers = []

        this.onClickHandlers.push((layout : W2UI.W2Tabs) => {
            // console.trace('me')
            layout.owner.html(panel, self.div[0])
        })

        this.tab.add({
            id : id,
            caption : caption,
            onClick : () => { self.onClick(this.tab) }
        })

        $(window).resize(() => {
            _(self.onResizeHandlers).each((h) => { h() })
        })
    }

    public captionShouldBeBold(bold : boolean) : void {
        this._captionShouldBeBold = bold
        this.refresh()
    }

    public click() : void {
        this.tab.click(this.id)
    }

    public onClick(layout : W2UI.W2Tabs) {
        this.captionShouldBeBold(false)
        _(this.onClickHandlers).each((h) => { h(layout) })
    }

    public onResize() {
        _(this.onResizeHandlers).each((h) => { h() })
    }

    public refresh() : void {
        const captionText = `${this.caption} ${this.captionSuffix}`
        this.tab.set(this.id, {
            caption : this._captionShouldBeBold ? `<b>${captionText}</b>`  : captionText
        })
        this.tab.refresh()
    }

    public setCaptionSuffix(s : string) : void {
        this.captionSuffix = s
        this.refresh()
    }

}
