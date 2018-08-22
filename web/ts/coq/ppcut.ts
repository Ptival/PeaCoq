abstract class PpCut { }

class PpBrk extends PpCut {
  constructor(public n1 : number, public n2 : number) { super() }
}

class PpTbrk extends PpCut {
  constructor(public n1 : number, public n2 : number) { super() }
}

class PpTab extends PpCut { }

class PpFnl extends PpCut { }
