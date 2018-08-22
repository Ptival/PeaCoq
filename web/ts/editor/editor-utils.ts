import { Strictly } from '../peacoq/strictly'

/**
 * Checks if first argument is strictly before second argument
**/
export function isBefore(flag : Strictly, pos1 : AceAjax.Position, pos2 : AceAjax.Position) : boolean {
  if (pos1.row < pos2.row) { return true }
  if (pos1.row > pos2.row) { return false }
  switch (flag) {
    case Strictly.Yes : return pos1.column < pos2.column
    case Strictly.No : return pos1.column <= pos2.column
  }
  throw 'EditorUtils.isBefore'
}
