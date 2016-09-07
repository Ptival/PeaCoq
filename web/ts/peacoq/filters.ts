import * as Feedback from "../coq/feedback";
import * as Stage from "../editor/stage";
import * as Answer from "../sertop/answer";
import * as Command from "../sertop/command";
import * as ControlCommand from "../sertop/control-command";

/*
I used to do this by overloading the type for filter as:
filter<U>(predicate: (value: T, index: number, source: Observable<T>) => boolean, thisArg?: any): Observable<U>;
But it makes tsc much much slower, which is unbearable.
*/

export function controlCommand(
  s: Rx.Observable<ISertop.ICommand>
): Rx.Observable<Command.Control<ISertop.IControlCommand>> {
  return (s as Rx.Observable<any>).filter(i => i instanceof Command.Control);
}

export function stmAdd(s: ControlCommand$): StmAdd$ {
  return (s as Rx.Observable<Command.Control<any>>).filter(i => i.controlCommand instanceof ControlCommand.StmAdd);
}

export function stmCancel(s: ControlCommand$): StmCancel$ {
  return (s as Rx.Observable<Command.Control<any>>).filter(i => i.controlCommand instanceof ControlCommand.StmCancel);
}

export function stmEditAt(s: ControlCommand$): StmEditAt$ {
  return (s as Rx.Observable<Command.Control<any>>).filter(i => i.controlCommand instanceof ControlCommand.StmEditAt);
}

export function stmQuery(s: ControlCommand$): StmQuery$ {
  return (s as Rx.Observable<Command.Control<any>>).filter(i => i.controlCommand instanceof ControlCommand.StmQuery);
}

export function sentenceBeingProcessed(
  s: Rx.Observable<ISentence<IStage>>
): Rx.Observable<ISentence<IBeingProcessed>> {
  return (s as Rx.Observable<ISentence<any>>).filter(i => i.stage instanceof Stage.BeingProcessed);
}

export function sentenceProcessed(
  s: Rx.Observable<ISentence<IStage>>
): Rx.Observable<ISentence<IProcessed>> {
  return (s as Rx.Observable<ISentence<any>>).filter(i => i.stage instanceof Stage.Processed);
}

export function beingProcessed(
  s: Rx.Observable<IStage>
): Rx.Observable<IBeingProcessed> {
  return (s as Rx.Observable<any>).filter(i => i instanceof Stage.BeingProcessed);
}

export function processed(
  s: Rx.Observable<IStage>
): Rx.Observable<IProcessed> {
  return (s as Rx.Observable<any>).filter(i => i instanceof Stage.Processed);
}

export function answer(
  s: Rx.Observable<ISertop.IAnswer<ISertop.IAnswerKind>>
): Rx.Observable<Answer.Answer> {
  return (s as Rx.Observable<any>).filter(i => i instanceof Answer.Answer);
}

export function feedback(
  s: Rx.Observable<ISertop.IAnswer<ISertop.IAnswerKind>>
): Rx.Observable<Feedback.Feedback> {
  return (s as Rx.Observable<any>).filter(i => i instanceof Feedback.Feedback);
}
