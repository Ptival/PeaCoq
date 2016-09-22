namespace CoqStringUtils {

  const delimiters = ["."]

  function my_index(str: string): number {
    const index: number = delimiters.reduce((indexAcc, delimiter) => {
      const pos = str.indexOf(delimiter)
      return (pos >= 0 && pos < index) ? pos : indexAcc
    }, +Infinity)
    return (index === +Infinity) ? -1 : index
  }

  const bullets = ["{", "}", "+", "-", "*"]

  export function isBullet(s: string): boolean { return _(bullets).includes(s) }

  export function next(str: string): number {
    // if the very next thing is one of {, }, +, -, *, it is the next
    const trimmed = coqTrimLeft(str)
    if (_(bullets).includes(trimmed[0])) {
      return str.length - trimmed.length + 1
    }
    // otherwise, gotta find a dot
    return coq_find_dot(coq_undot(str), 0) + 1
  }

  // TODO: this is a bit hacky (but I guess I'm not using it anymore)
  // function prev(str) {
  //   // remove the last delimiter, since we are looking for the previous one
  //   str = str.substring(0, str.length - 1)
  //   const lastDotPosition = coq_find_last_dot(coq_undot(str), 0)
  //   // now, it could be the case that there is a bulconst after that dot
  //   const strAfterDot = str.substring(lastDotPosition + 1, str.length)
  //   const firstCharAfterDot = coqTrimLeft(strAfterDot)[0]
  //   if (_(bullets).includes(firstCharAfterDot)) {
  //     return lastDotPosition + 1 + strAfterDot.indexOf(firstCharAfterDot) + 1
  //   }
  //   // otherwise, find the last dot
  //   return coq_find_last_dot(coq_undot(str), 0) + 1
  // }

  function count(str: string, pat: string): number {
    const arr = str.split(pat)
    return (arr.length)
  }

  // highlight dot that are terminators as opposed to the others
  function coq_undot(str: string): string {
    str = str.replace(/[.][.][.]/g, "__.") // emphasize the last dot of ...
    str = str.replace(/[.][.]/g, "__") // hides .. in notations
    str = str.replace(/[.][a-zA-Z1-9_\(]/g, "__") // hides qualified identifiers
    // hide curly braces that are implicit arguments
    // str = str.replace(/\{((?:[^\.\}]|\.(?!\s))*)\}/g, "_$1_")
    // make other braces look like periods
    // str = str.replace(/[\{\}]/g, ".")
    return str
  }

  function coq_find_dot(str: string, toclose: number): number {
    const index = my_index(str)
    if (index === -1) {
      return index
    }
    const tocheck = str.substring(0, index)
    const opened = count(tocheck, "(*") + toclose - count(tocheck, "*)")
    if (opened <= 0) {
      return index
    } else {
      const newindex = coq_find_dot(str.substring(index + 1), opened)
      if (newindex === -1) { return -1 }
      return index + newindex + 1
    }
  }

  // TODO: rewrite this in functional style
  function coq_get_last_dot(str: string): number {
    let modified = str
    let index = -1
    while (my_index(modified) >= 0) {
      index = my_index(modified)
      modified = modified.substring(0, index) + " " +
        modified.substring(index + 1)
    }
    return index
  }

  function coq_find_last_dot(str: string, toopen: number): number {
    const index = coq_get_last_dot(str)
    if (index === -1) {
      return index
    }
    const tocheck = str.substring(index + 1)
    const closed = count(tocheck, "*)") + toopen - count(tocheck, "(*")
    if (closed <= 0) {
      return index
    } else {
      const newindex = coq_find_last_dot(str.substring(0, index), closed)
      return newindex
    }
  }

  // TODO: rewrite this in functional style
  function stripComments(s: string): string {
    let output = ""
    let commentDepth = 0
    let pos = 0
    while (pos < s.length) {
      const sub = s.substring(pos)
      if (sub.startsWith("(*")) {
        commentDepth++
        pos += 2
      } else if (sub.startsWith("*)")) {
        commentDepth--
        pos += 2
      } else if (commentDepth > 0) {
        pos++
      } else {
        output += s[pos]
        pos++
      }
    }
    return output
  }

  export function coqTrim(s: string): string {
    if (s.length > 10000) {
      alert("WARNING: Performing coqTrim on large string")
    }
    return stripComments(s).trim()
  }

  // TODO: rewrite this in functional style
  export function coqTrimLeft(s: string): string {
    let commentDepth = 0
    let pos = 0
    while (pos < s.length) {
      const sub = s.substring(pos)
      if (sub.startsWith("(*")) {
        commentDepth++
        pos += 2
      } else if (sub.startsWith("*)")) {
        commentDepth--
        pos += 2
      } else if (commentDepth > 0) {
        pos++
      } else if (sub[0] === " " || sub[0] === "\n") {
        pos++
      } else {
        return sub
      }
    }
    return ""
  }

  // TODO: rewrite this in functional style
  function coqTrimRight(s: string): string {
    let commentDepth = 0
    let pos = s.length - 1
    while (pos > 0) {
      const sub = s.substring(0, pos)
      const lastChar = sub[sub.length - 1]
      if (sub.endsWith("*)")) {
        commentDepth++
        pos -= 2
      } else if (sub.endsWith("(*")) {
        commentDepth--
        pos -= 2
      } else if (commentDepth > 0) {
        pos--
      } else if (lastChar === " " || lastChar === "\n") {
        pos--
      } else {
        return sub
      }
    }
    return ""
  }

}
