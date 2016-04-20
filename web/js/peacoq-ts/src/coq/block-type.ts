export default BlockType;

export abstract class BlockType { }

export class PpHBox extends BlockType {
  constructor(public x: number) {
    super();
  }
}

export class PpVBox extends BlockType {
  constructor(public x: number) {
    super();
  }
}

export class PpHVBox extends BlockType {
  constructor(public x: number) {
    super();
  }
}

export class PpHoVBox extends BlockType {
  constructor(public x: number) {
    super();
  }
}

export class PpTBox extends BlockType { }
