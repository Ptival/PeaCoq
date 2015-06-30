/* Helpers */

function assignThis(res, t, a) {
    assert(t !== undefined, "assign, missing contents");
    assert(t.length === a.length, "length mismatch");
    _(a).each(function(field, ndx) {
        res[field] = t[ndx];
    });
}

function assign(t, a) {
    var res = {};
    assignThis(res, t, a);
    return res;
}

function isVar(term, name) {
    return term.constructor === Var && (name ? term.name === name : true);
}

function isNeq(term) {
    return (
        isVar(term.left, "not")
            && isInfixBinaryOperation(term.right, "eq")
    );
}

var binaryOperations = [
    "and",
    "andb",
    "concat",
    "cons",
    "eq",
    "equiv",
    "or",
    "orb",
    "minus",
    "mult",
    "plus",
];

function isInfixBinaryOperation(term, name) {
    var res = (
        term.constructor === App
            && term.left.constructor === App
            && term.left.left.constructor === Var
            && _(binaryOperations).contains(term.left.left.name)
            && (name ? term.left.left.name === name : true)
    );
    return (
        term.constructor === App
            && term.left.constructor === App
            && term.left.left.constructor === Var
            && _(binaryOperations).contains(term.left.left.name)
            && (name ? term.left.left.name === name : true)
    );
}

function getInfixBinaryOperation(term) {
    if (isInfixBinaryOperation(term)) {
        return term.left.left;
    } else {
        return undefined;
    }
}

/*
 * Returns a jQuery Element ready to receive any Term HTML.
 */
function mkTermHTML(term) {
    return $("<span>")
        .addClass("term")
        .data("term", term)
    ;
}

function syntax(s) {
    return $("<span>").addClass("syntax").text(s);
}

function quantifierHTML(quantifier, binders, body) {
    var res = mkTermHTML(this);
    res
        .append(syntax("∀"))
        .append(" ")
    ;
    _(binders).each(function(binder, ndx) {
        if (ndx > 0) { res.append(" "); }
        res.append(binder.toHTML());
    });
    res
        .append(syntax(","))
        .append(" ")
        .append(body.toHTML())
    ;
    return res;
}

/* Precedences */

var prec = 0;
var precMin = prec++;

var precEquiv  = prec++;
var precArrow  = prec++;
var precOr     = prec++;
var precAnd    = prec++;
var precNeg    = prec++;
var precEq     = prec++;
var precNeq    = precEq;
var precCons   = prec++;
var precConcat = prec++;
var precOrb    = prec++;
var precAndb   = prec++;
var precLt     = prec++;
var precGt     = precLt;
var precLe     = precLt;
var precGe     = precLt;
var precPlus   = prec++;
var precMinus  = precPlus;
var precMult   = prec++;
var precLParen = prec++;
var precRParen = precLParen;
var precLBrace = prec++;
var precRBrace = precLBrace;
var precVar    = prec++;
var precForall = precVar;
var precExists = precVar;
var precLambda = precVar;
var precMatch  = precVar;
var precLet    = precVar;
var precApp    = prec++;

var precMax = prec++;

/* Associativities */

var assocEquiv  = "left";
var assocArrow  = "right";
var assocOr     = "right";
var assocAnd    = "right";
var assocCons   = "right";
var assocConcat = "right";
var assocOrb    = "left";
var assocAndb   = "left";
var assocPlus   = "left";
var assocMinus  = "left";
var assocMult   = "left";

/* Term */

function mkTerm(t) {
    switch(t.tag) {
    case "Var":       return new Var(t);
    case "Forall":    return new Forall(t);
    case "Lambda":    return new Lambda(t);
    case "Exists":    return new Exists(t);
    case "Arrow":     return new Arrow(t);
    case "App":       return new App(t);
    case "Match":     return new Match(t);
    case "Let":       return new Let(t);
    case "LetParent": return new LetParen(t);
    case "Raw":       return new Raw(t);
    default:
        alert("Unknown tag: " + t.tag + ", see log for more information.");
        console.log("Unknown tag for term: ", t);
    };
}

function Term() {
    this.folded = true;
}

function Var(t) {
    Term.call(this);
    this.folded = false; // no point in folding variables
    this.name = t.contents;
}

Var.prototype = Object.create(Term.prototype);
Var.prototype.constructor = Var;

Var.prototype.getPrecedence = function() {
    return precVar;
}

Var.prototype.getAssociativity = function() {
    switch (this.name) {
    case "equiv":  return assocEquiv;
    case "or":     return assocOr;
    case "and":    return assocAnd;
    case "cons":   return assocCons;
    case "concat": return assocConcat;
    case "orb":    return assocOrb;
    case "andb":   return assocAndb;
    case "plus":   return assocPlus;
    case "minus":  return assocMinus;
    case "mult":   return assocMult;
    default:
        alert("No associativity for: " + this.name);
        throw new Error("No associativity for: " + this.name);
    }
}

Var.prototype.toString = function() {
    return this.name;
}

Var.prototype.toHTML = function() {
    return (
        mkTermHTML(this)
            .append(this.name)
    );
}

function Forall(t) {
    Term.call(this);
    assignThis(this, t.contents, ["binders", "body"]);
    this.binders = _(this.binders).map(function(binder) {
        return new Binder(binder);
    }).value();
    this.body = mkTerm(this.body);
}

Forall.prototype = Object.create(Term.prototype);
Forall.prototype.constructor = Forall;

Forall.prototype.getPrecedence = function() {
    return precForall;
}

Forall.prototype.toString = function() {
    return (
        "∀ "
            + _(this.binders).reduce(function(acc, binder, ndx) {
                return (
                    (ndx > 0 ? " " : "")
                        + binder.toString()
                );
            }, "")
            + ", "
            + this.body.toString()
    );
}

Forall.prototype.toHTML = function() {
    return quantifierHTML("∀", this.binders, this.body);
}

function Lambda(t) {
    Term.call(this);
    assignThis(this, t, ["binders", "body"]);
    this.binders = _(this.binders).map(function(binder) {
        return new Binder(binder);
    }).value();
    this.body = mkTerm(this.body);
}

Lambda.prototype = Object.create(Term.prototype);
Lambda.prototype.constructor = Lambda;

Lambda.prototype.getPrecedence = function() {
    return precLambda;
}

Lambda.prototype.toString = function() {
    return (
        "λ "
            + _(this.binders).reduce(function(acc, binder, ndx) {
                return (
                    (ndx > 0 ? " " : "")
                        + binder.toString()
                );
            }, "")
            + ", "
            + this.body.toString()
    );
}

Lambda.prototype.toHTML = function() {
    return quantifierHTML("λ", this.binders, this.body);
}

function Exists(t) {
    Term.call(this);
    assignThis(this, t.contents, ["binders", "body"]);
    this.binders = _(this.binders).map(function(binder) {
        return new Binder(binder);
    }).value();
    this.body = mkTerm(this.body);
}

Exists.prototype = Object.create(Term.prototype);
Exists.prototype.constructor = Exists;

Exists.prototype.getPrecedence = function() {
    return precExists;
}

Exists.prototype.toString = function() {
    return (
        "∃ "
            + _(this.binders).reduce(function(acc, binder, ndx) {
                return (
                    (ndx > 0 ? " " : "")
                        + binder.toString()
                );
            }, "")
            + ", "
            + this.body.toString()
    );
}

Exists.prototype.toHTML = function() {
    return quantifierHTML("∃", this.binders, this.body);
}

function Arrow(t) {
    Term.call(this);
    assignThis(this, t.contents, ["left", "right"]);
    this.left  = mkTerm(this.left);
    this.right = mkTerm(this.right);
}

Arrow.prototype = Object.create(Term.prototype);
Arrow.prototype.constructor = Arrow;

Arrow.prototype.getPrecedence = function() {
    return precArrow;
}

Arrow.prototype.toString = function() {
    var res = "";

    switch (this.left.constructor) {
        // need parentheses
    case Arrow: // Arrow is right-associative
    case Exists:
    case Forall:
    case Let:
    case LetParen:
        res += "(" + this.left.toString() + ")";
        break;
        // no need for parentheses
    case App:
    case Match:
    case Var:
        res += this.left.toString();
        break;
    case Lambda:
        throw new Error("This should not happen");
    default:
        throw new Error("Unknown Term: " + this.left);
    };

    res += " → ";

    switch (this.right.constructor) {
        // no need for parentheses
    case App:
    case Arrow: // Arrow is right-associative
    case Exists:
    case Forall:
    case Let:
    case LetParen:
    case Match:
    case Var:
        res += this.right.toString();
        break;
    case Lambda:
        throw new Error("This should not happen");
    default:
        throw new Error("Unknown Term: " + this.right);
    };

    return res;
}

Arrow.prototype.toHTML = function() {
    return quantifierHTML("∃", this.binders, this.body);
}

function App(t) {
    Term.call(this);
    assignThis(this, t.contents, ["left", "right"]);
    this.left  = mkTerm(this.left);
    this.right = mkTerm(this.right);
}

App.prototype = Object.create(Term.prototype);
App.prototype.constructor = App;

App.prototype.getPrecedence = function() {
    /* fully-applied infix binary operators */
    var binOp = getInfixBinaryOperation(this);
    if (binOp) {
        switch (binOp.name) {
        case "or":     return precOr;
        case "and":    return precAnd;
        case "neg":    return precNeg;
        case "eq":     return precEq;
        case "neq":    return precNeq;
        case "cons":   return precCons;
        case "concat": return precConcat;
        case "orb":    return precOrb;
        case "andb":   return precAndb;
        case "lt":     return precLt;
        case "gt":     return precGt;
        case "le":     return precLe;
        case "ge":     return precGe;
        case "plus":   return precPlus;
        case "minus":  return precMinus;
        case "mult":   return precMult;
        default: break;
        };
    } else if (isNeq(this)) {
        return precNeq;
    } else {
        return precApp;
    }
}

function binOpString(name) {
    switch (name) {
    case "equiv":  return "<->";
    case "or":     return "∨";
    case "and":    return "∧";
    case "eq":     return "=";
    case "neq":    return "≠";
    case "cons":   return "::";
    case "concat": return "++";
    case "orb":    return "||";
    case "andb":   return "&&";
    case "lt":     return "<";
    case "le":     return "<=";
    case "gt":     return ">";
    case "ge":     return ">=";
    case "plus":   return "+";
    case "minus":  return "-";
    case "mult":
    case "prod":   return "*";
    default:
        throw new Error("No binary operator string for: " + name);
    }
}

function par(term, parentTerm) {
    var parentPrec = parentTerm.getPrecedence();
    var termPrec = term.getPrecedence();
    /* namely, if the precedence of the inner operator is lower, then
     * we need to put parentheses */
    if (termPrec <= parentPrec) {
        return "(" + term.toString() + ")";
    } else {
        return term.toString();
    }
}

function parAssoc(term) {
    var assoc = term.left.left.getAssociativity();
    switch (assoc) {
    case "left":
        // no need for parentheses
        return term.toString();
        break;
    case "right":
        // need parentheses
        return "(" + term.toString() + ")";
        break;
    default:
        throw new Error("Bad associativity: " + assoc);
    };
}

App.prototype.toString = function() {
    var res = "";

    var thisPrec = this.getPrecedence();
    var topBinOp = getInfixBinaryOperation(this);
    if (topBinOp) {

        var leftBinOp = getInfixBinaryOperation(this.left.right);
        if (leftBinOp) {
            if (leftBinOp.name === topBinOp.name) {
                // same nested infix binary operators, use associativity
                res += parAssoc(this.left.right);
            } else {
                // different nested infix binary operators, use precedence
                res += par(this.left.right, this);
            }
        } else {
            // left operand is not an infix binary operator
            res += par(this.left.right, this);
        }

        res += " " + binOpString(topBinOp.name) + " ";

        var rightBinOp = getInfixBinaryOperation(this.right)
        if (rightBinOp) {
            if (rightBinOp.name === topBinOp.name) {
                // same nested infix binary operators, use associativity
                res += parAssoc(this.right);
            } else if (rightBinOp) {
                // different nested infix binary operators, use precedence
                res += par(this.right, this);
            }
        } else {
            res += par(this.right, this);
        }

    } else if (isNeq(this)) { // not (eq a b) should print a ≠ b

        res += par(this.right.left.right, this);
        res += " ≠ ";
        res += par(this.right.right, this);

    } else {

        res += par(this.left, this) + " " + par(this.right, this);

    }

    return res;





    var topBinOp = this.isFullyAppliedBinaryOperator();
    /* fully-applied infix binary operators */
    if (topBinOp) {

        var leftBinOp = this.left.right.isFullyAppliedBinaryOperator();
        if (leftBinOp && leftBinOp.name === topBinOp.name) {
            var assoc = leftBinOp.getAssociativity();
            switch (assoc) {
            case "left":
                // no need for parentheses
                res += this.left.right.toString();
                break;
            case "right":
                // need parentheses
                res += "(" + this.left.right.toString() + ")";
                break;
            default:
                throw new Error("Bad associativity: " + assoc);
            };
        } else if (leftBinOp !== undefined) {
            // nested but different operators, precedence matters
            /* namely, if the precedence of the inner operator is
             * lower, then we need to put parentheses */
            var outerPrec = topBinOp.getPrecedence();
            var innerPrec = this.left.right.left.left.getPrecedence();
            if (innerPrec <= outerPrec) {
                // need parentheses
                res += "(" + this.left.right.toString() + ")";
            } else {
                // no need for parentheses
                res += this.left.right.toString();
            }
        } else {
            // left operand is not a fully-applied binary operator
            switch (this.left.constructor) {
                // need parentheses
            case Arrow:
            case Exists:
            case Forall:
            case Lambda:
            case Let:
            case LetParen:
                res += "(" + this.left.right.toString() + ")";
                break;
                // no need for parentheses              
            case App: // App is left-associative
            case Match:
            case Var:
                res += this.left.right.toString();
                break;
            default:
                throw new Error("Unknown Term: " + this.left);
            };
        }

        res += " " + binOpString(topBinOp.name) + " ";

        var rightBinOp = this.right.isFullyAppliedBinaryOperator();
        if (rightBinOp && rightBinOp.name === topBinOp.name) {
            var assoc = rightBinOp.getAssociativity();
            switch (assoc) {
            case "left":
                // need parentheses
                res += "(" + this.right.toString() + ")";
                break;
            case "right":
                // no need for parentheses
                res += this.right.toString();
                break;
            default:
                throw new Error("Bad associativity: " + assoc);
            };
        } else if (rightBinOp !== undefined) {
            // nested but different operators, precedence matters
            /* namely, if the precedence of the inner operator is
             * lower, then we need to put parentheses */
            var outerPrec = topBinOp.getPrecedence();
            var innerPrec = this.right.left.left.getPrecedence();
            if (innerPrec <= outerPrec) {
                // need parentheses
                res += "(" + this.right.toString() + ")";
            } else {
                // no need for parentheses
                res += this.right.toString();
            }
        } else {
            // right operand is not a fully-applied binary operator
            switch (this.right.constructor) {
                // need parentheses
            case App: // App is left-associative
            case Arrow:
            case Exists:
            case Forall:
            case Lambda:
            case Let:      // not needed, but Coq prints it
            case LetParen: // not needed, but Coq prints it
                res += "(" + this.right.toString() + ")";
                break;
                // no need for parentheses              
            case Match:
            case Var:
                res += this.right.toString();
                break;
            default:
                throw new Error("Unknown Term: " + this.right);
            }
        }
        

    } else {
        
        switch (this.left.constructor) {
            // need parentheses
        case Forall:
        case Lambda:
        case Exists:
        case Arrow:
        case Let:
        case LetParen:
            res += "(" + this.left.toString() + ")";
            break;
            // no need for parentheses
        case Var:
        case App: // App is left-associative
        case Match:
            res += this.left.toString();
            break;
        default:
            throw new Error("Unknown Term: " + this.left);
        };

        res += " ";
        
        switch (this.right.constructor) {
            // need parentheses
        case Forall:
        case Lambda:
        case Exists:
        case Arrow:
        case Let:
        case LetParen:
        case App: // App is left-associative
            res += "(" + this.left.toString() + ")";
            break;
            // no need for parentheses
        case Var:
        case Match:
            res += this.left.toString();
            break;
        default:
            throw new Error("Unknown Term: " + this.left);
        };
        
    }

    return res;
}

function Match(t) {
    Term.call(this);
    assignThis(this, t.contents, ["items", "maybeType", "equations"]);
    this.maybeType = this.maybeType ? mkTerm(this.maybeType) : undefined;
}

Match.prototype = Object.create(Term.prototype);
Match.prototype.constructor = Match;

Match.prototype.getPrecedence = function() {
    return precMatch;
}

Match.prototype.toString = function() {
    return "match ... end";
}

function Let(t) {
    Term.call(this);
    assignThis(this, t.contents, ["name", "binders", "maybeType", "bindee", "body"]);
    this.maybeType = this.maybeType ? mkTerm(this.maybeType) : undefined;
    this.bindee = mkTerm(this.bindee);
    this.body = mkTerm(this.body);
}

Let.prototype = Object.create(Term.prototype);
Let.prototype.constructor = Let;

Let.prototype.getPrecedence = function() {
    return precLet;
}

Let.prototype.toString = function() {
    return "let ... = ... in ...";
}

function LetParen(t) {
    Term.call(this);
    assignThis(this, t.contents, ["names", "maybeType", "bindee", "body"]);
    this.maybeType = this.maybeType ? mkTerm(this.maybeType) : undefined;
    this.bindee = mkTerm(this.bindee);
    this.body = mkTerm(this.body);
}

LetParen.prototype = Object.create(Term.prototype);
LetParen.prototype.constructor = LetParen;

LetParen.prototype.getPrecedence = function() {
    return precLet;
}

LetParen.prototype.toString = function() {
    return "let (...) = ... in ...";
}

function Raw(t) {
    Term.call(this);
    this.raw = t;
}

Raw.prototype = Object.create(Term.prototype);
Raw.prototype.constructor = Raw;

Raw.prototype.toString = function() {
    return this.raw;
}

/* Binder */

function Binder(t) {
    assignThis(this, t, ["maybeNames", "maybeType"]);
    this.maybeType = this.maybeType ? mkTerm(this.maybeType) : undefined;
}

Binder.prototype.toString = function() {
    var res = "";

    _(this.maybeNames).each(function(maybeName, ndx) {
        if (ndx > 0) { res += " "; }
        res += maybeName ? maybeName : "_";
    });

    if (this.maybeType !== undefined) {
        res = "(" + res + " : " + this.maybeType.toString() + ")";
    }

    return res;
}
