interface IStage {
  marker: ISentenceMarker;
  getColor(): string;
  getStateId(): Maybe<number>;
}

interface IToProcess extends IStage {
  nextStageMarker(): ISentenceMarker;
}

interface WithStateId {
  stateId: number;
}

interface IBeingProcessed extends IStage, WithStateId {
  nextStageMarker(): ISentenceMarker;
}

interface IProcessed extends IStage, WithStateId {
  // context: PeaCoqContext | null;
  // editId: number;
  // goals: Maybe<IGoals>;
  //status: IStatus;
  getContext(): Promise<PeaCoqContext>;
  setContext(c: PeaCoqContext): void;
}
