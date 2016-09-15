// TODO: the thing causing this import should go elsewhere
import { Warning } from "../coq/message-level"

function isQueryWarning(m: IMessage) {
  return (
    m.level.constructor === Warning && m.content.indexOf(
      "Query commands should not be inserted in scripts"
    ) > -1
  )
}

function parentHeight(): string {
  return $(this).parent().css("height")
}

function halfParentHeight(): string {
  return (parseInt($(this).parent().css("height"), 10) / 2) + "px"
}

function resetCoqtop(): Promise<any> {
  return Promise.resolve()
  // return peaCoqEditAt(1)
  //   .then(() => peaCoqAddPrime("Require Import PeaCoq.PeaCoq."))
  //   .then(() => peaCoqStatus(false))
}

export function sameBodyAndType(hyp1: HTMLElement, hyp2: HTMLElement): boolean {
  let children1 = $(hyp1).children().slice(1)
  let children2 = $(hyp2).children().slice(1)
  if (children1.length !== children2.length) { return false }
  for (let i in _.range(children1.length)) {
    if ($(children1[i]).html() !== $(children2[i]).html()) {
      return false
    }
  }
  return true
}

function capitalize(s: string): string {
  return s.charAt(0).toUpperCase() + s.slice(1)
}
