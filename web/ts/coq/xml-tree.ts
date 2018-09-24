import * as _ from 'lodash'
import { Maybe } from 'tsmonad'

import { C_AST } from './lib/c-ast'
import * as Loc from './lib/loc'

class CoqXMLTree {
    public rootLabel : C_AST<CoqXMLTag>
    public subForest : CoqXMLTree[]
    constructor(t : [Loc.T, ICoqtopResponse<any>]) {
        const [loc, xmltag] = t
        this.rootLabel = new C_AST(mkCoqXMLTag(xmltag), Maybe.just(loc))
        this.subForest = _(t[1]).map((t : [Loc.T, ICoqtopResponse<any>]) => {
            return new CoqXMLTree(t)
        }).value()
    }
    public toString(depth : number) {
        let res = ''
        if (typeof depth === 'undefined') {
            depth = 0
        }
        _(_.range(depth)).each(() => {
            res += '  '
        })
        res += '`- ' + this.rootLabel.toString() + '\n'
        _(this.subForest).each((t : CoqXMLTree) => {
            res += t.toString(depth + 1)
        })
        return res
    }
}
