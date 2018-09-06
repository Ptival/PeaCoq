/*
  The pretty-printed context exposes objects of the form :
  { constructorName : 'Constructor',
  constructorArgs : [a1, ...] }
  Where the `a`s may be numerals, strings, arrays or objects
*/

import * as PpExtend from '../coq/interp/ppextend'
import * as ConstrExpr from '../coq/intf/constr-expr'
import * as LibNames from '../coq/library/libnames'

function assert(condition : boolean, message : string) : void {
    if (!condition) {
        debugger
        throw message
    }
}

type IsValidArg<T> = T extends object ? keyof T extends never ? false : true : true
type IsArg1Valid<T, E> = T extends (arg : infer U) => void ? IsValidArg<U> extends true ? {} : E : E

function ctor0<C>(ctor : new () => C, args : any[]) : C {
    assert(args.length === 0, 'ctor0: ${ctor}, ${args}')
    return new ctor()
}

function ctor1<C>(ctor : new (a : any) => C, args : any[]) : C {
    assert(args.length === 1, `ctor1: ${ctor}, ${args}`)
    const [a] = args
    return new ctor(a)
}

function ctor2<C>(ctor : new (a : any, b : any) => C, args : any[]) : C {
    assert(args.length === 2, 'ctor2: ${ctor}, ${args}')
    const [a, b] = args
    return new ctor(a, b)
}

function ctor3<C>(ctor : new (a : any, b : any, c : any) => C, args : any[]) : C {
    assert(args.length === 3, 'ctor3: ${ctor}, ${args}')
    const [a, b, c] = args
    return new ctor(a, b, c)
}

function ctor4<C>(ctor : new (a : any, b : any, c : any, d : any) => C, args : any[]) : C {
    assert(args.length === 4, 'ctor4: ${ctor}, ${args}')
    const [a, b, c, d] = args
    return new ctor(a, b, c, d)
}

function ctor5<C>(ctor : new (a : any, b : any, c : any, d : any, e : any) => C, args : any[]) : C {
    assert(args.length === 5, 'ctor5: ${ctor}, ${args}')
    const [a, b, c, d, e] = args
    return new ctor(a, b, c, d, e)
}

export function walkJSON(input : any) : any {
    // console.log(input)
    if (typeof input === 'object') {
        if (input.hasOwnProperty('constructorName')) {
            const processedArgs = input.constructorArgs.map(walkJSON)
            switch (input.constructorName) {

                    // special case for nothing
                case 'nothing'  : return nothing()

                    // coq-constr-expr
                case 'CApp'        : return ctor2(ConstrExpr.CApp,        processedArgs)
                case 'CLocalAssum' : return ctor3(ConstrExpr.CLocalAssum, processedArgs)
                case 'CNotation'   : return ctor4(ConstrExpr.CNotation,   processedArgs)
                case 'CPrim'       : return ctor1(ConstrExpr.CPrim,       processedArgs)
                case 'CProdN'      : return ctor2(ConstrExpr.CProdN,      processedArgs)
                case 'CRef'        : return ctor2(ConstrExpr.CRef,        processedArgs)

                case 'Default'     : return ctor1(Default,     processedArgs)
                case 'Explicit'    : return ctor0(Explicit,    processedArgs)

                    // libnames
                case 'Ident'       : return ctor1(LibNames.Ident,  processedArgs)
                case 'Qualid'      : return ctor1(LibNames.Qualid, processedArgs)


                case 'Name'        : return ctor1(Name,        processedArgs)
                case 'Numeral'     : return ctor2(Numeral,     processedArgs)
                case 'E'           : return ctor0(E,           processedArgs)
                case 'L'           : return ctor0(L,           processedArgs)

                case 'PpBrk' : {
                    const [a, b] = processedArgs
                    return new PpExtend.PpBrk(a, b)
                }
                case 'PpHoVB' : {
                    const [a] = processedArgs
                    return new PpExtend.PpHoVB(a)
                }
                case 'Prec' : {
                    const [a] = processedArgs
                    return new Prec(a)
                }
                case 'UnpBox' : {
                    const [a, b] = processedArgs
                    return new PpExtend.UnpBox(a, b)
                }
                case 'UnpCut' : {
                    const [a] = processedArgs
                    return new PpExtend.UnpCut(a)
                }
                case 'UnpMetaVar' : {
                    const [a, b] = processedArgs
                    return new PpExtend.UnpMetaVar(a, b)
                }
                case 'UnpTerminal' : {
                    const [a] = processedArgs
                    return new PpExtend.UnpTerminal(a)
                }

                default :
                    const showme = input.constructorName
                    const len = input.constructorArgs.length
                    debugger
            }
            // return new (eval(input.constructorName))(...processedArgs)
        }
        if (Array.isArray(input)) {
            return input.map(walkJSON)
        }
        const output : any = {}
        for (const k in input) {
            output[k] = walkJSON(input[k])
        }
        return output
    }
    if (['boolean', 'number', 'string'].includes(typeof input)) {
        return input
    }
    debugger
    return input
}
