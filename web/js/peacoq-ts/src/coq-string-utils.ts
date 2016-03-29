let delimiters = ["."];

function my_index(str) {
  let index = +Infinity;
  _(delimiters).each(function(delimiter) {
    let pos = str.indexOf(delimiter);
    if (pos >= 0 && pos < index) {
      index = pos;
    }
  });
  if (index !== +Infinity) {
    return index;
  } else {
    return -1;
  }
}

let bullets = ["{", "}", "+", "-", "*"];

function next(str) {
  // if the very next thing is one of {, }, +, -, *, it is the next
  let trimmed = coqTrimLeft(str);
  if (_(bullets).includes(trimmed[0])) {
    return str.length - trimmed.length + 1;
  }
  // otherwise, gotta find a dot
  return coq_find_dot(coq_undot(str), 0) + 1;
}

// TODO: this is a bit hacky
function prev(str) {
  // remove the last delimiter, since we are looking for the previous one
  str = str.substring(0, str.length - 1);
  let lastDotPosition = coq_find_last_dot(coq_undot(str), 0);
  // now, it could be the case that there is a bullet after that dot
  let strAfterDot = str.substring(lastDotPosition + 1, str.length);
  let firstCharAfterDot = coqTrimLeft(strAfterDot)[0];
  if (_(bullets).includes(firstCharAfterDot)) {
    return lastDotPosition + 1 + strAfterDot.indexOf(firstCharAfterDot) + 1;
  }
  // otherwise, find the last dot
  return coq_find_last_dot(coq_undot(str), 0) + 1;
}

function count(str, pat) {
  let arr = str.split(pat);
  return (arr.length);
}

// highlight dot that are terminators as opposed to the others
function coq_undot(str) {
  str = str.replace(/[.][.][.]/g, "__."); // emphasize the last dot of ...
  str = str.replace(/[.][.]/g, "__"); // hides .. in notations
  str = str.replace(/[.][a-zA-Z1-9_\(]/g, "__"); // hides qualified identifiers
  // hide curly braces that are implicit arguments
  //str = str.replace(/\{((?:[^\.\}]|\.(?!\s))*)\}/g, "_$1_");
  // make other braces look like periods
  //str = str.replace(/[\{\}]/g, ".");
  return str;
}

function coq_find_dot(str, toclose) {
  let index = my_index(str);
  if (index == -1) {
    return index;
  }
  let tocheck = str.substring(0, index);
  let opened = count(tocheck, "(*") + toclose - count(tocheck, "*)");
  if (opened <= 0) {
    return index;
  } else {
    let newindex = coq_find_dot(str.substring(index + 1), opened);
    if (newindex == -1) { return -1; }
    return index + newindex + 1;
  }
}

function coq_get_last_dot(str) {
  let modified = str;
  let index = -1;
  while (my_index(modified) >= 0) {
    index = my_index(modified);
    modified = modified.substring(0, index) + " " +
      modified.substring(index + 1);
  }
  return index;
}

function coq_find_last_dot(str, toopen) {
  let index = coq_get_last_dot(str);
  if (index == -1) {
    return index;
  }
  let tocheck = str.substring(index + 1);
  let closed = count(tocheck, "*)") + toopen - count(tocheck, "(*");
  if (closed <= 0) {
    return index;
  } else {
    let newindex = coq_find_last_dot(str.substring(0, index), closed);
    return newindex;
  }
}

function stripComments(s) {
  let output = "";
  let commentDepth = 0;
  let pos = 0;
  while (pos < s.length) {
    let sub = s.substring(pos);
    if (sub.startsWith("(*")) {
      commentDepth++;
      pos += 2;
    } else if (sub.startsWith("*)")) {
      commentDepth--;
      pos += 2;
    } else if (commentDepth > 0) {
      pos++;
    } else {
      output += s[pos];
      pos++;
    }
  }
  return output;
}

function coqTrim(s) {
  if (s.length > 10000) {
    alert("WARNING: Performing coqTrim on large string");
  }
  return stripComments(s).trim();
}

function coqTrimLeft(s) {
  let commentDepth = 0;
  let pos = 0;
  while (pos < s.length) {
    let sub = s.substring(pos);
    if (sub.startsWith("(*")) {
      commentDepth++;
      pos += 2;
    } else if (sub.startsWith("*)")) {
      commentDepth--;
      pos += 2;
    } else if (commentDepth > 0) {
      pos++;
    } else if (sub[0] === " " || sub[0] === "\n") {
      pos++;
    } else {
      return sub;
    }
  }
  return "";
}

function coqTrimRight(s: string): string {
  let commentDepth = 0;
  let pos = s.length - 1;
  while (pos > 0) {
    let sub = s.substring(0, pos);
    let lastChar = sub[sub.length - 1];
    if (sub.endsWith("*)")) {
      commentDepth++;
      pos -= 2;
    } else if (sub.endsWith("(*")) {
      commentDepth--;
      pos -= 2;
    } else if (commentDepth > 0) {
      pos--;
    } else if (lastChar === " " || lastChar === "\n") {
      pos--;
    } else {
      return sub;
    }
  }
  return "";
}
