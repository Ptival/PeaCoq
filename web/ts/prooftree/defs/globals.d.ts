//cf. https://github.com/Microsoft/TypeScript/issues/7352#issuecomment-191547232

export declare enum MaybeType {
    Nothing = 0,
    Just = 1,
}

export interface MaybePatterns<T, U> {
    just: (t: T) => U
    nothing: () => U
}

export declare type OptionalMaybePatterns<T, U> = Partial<MaybePatterns<T, U>>;

export declare function maybe<T>(t: T): Maybe<T>;

declare namespace TsMonad {

    export class Maybe<T> { // implements Monad<T>, Functor<T>, Eq<Maybe<T>> {
        private type;
        private value;
        constructor(type: MaybeType, value?: T);
        static sequence<T>(t: {
            [k: string]: Maybe<T>;
        }): Maybe<{
            [k: string]: T;
        }>;
        static all: (t: {
            [k: string]: Maybe<any>;
        }) => Maybe<{
            [k: string]: any;
        }>;
        static maybe<T>(t?: T | null): Maybe<T>;
        static just<T>(t: T): Maybe<T>;
        static nothing<T>(): Maybe<T>;
        static isJust<T>(t: Maybe<T>): boolean;
        static isNothing<T>(t: Maybe<T>): boolean;
        unit<U>(u: U): Maybe<U>;
        bind<U>(f: (t: T) => Maybe<U>): Maybe<U>;
        of: <U>(u: U) => Maybe<U>;
        chain: <U>(f: (t: T) => Maybe<U>) => Maybe<U>;
        fmap<U>(f: (t: T) => U): Maybe<U>;
        lift: <U>(f: (t: T) => U) => Maybe<U>;
        map: <U>(f: (t: T) => U) => Maybe<U>;
        caseOf<U>(patterns: MaybePatterns<T, U>): U;
        defaulting(defaultValue: T): Maybe<T>;
        equals(other: Maybe<T>): any;
        valueOr<U extends T>(defaultValue: U): T | U;
        valueOrCompute<U extends T>(defaultValueFunction: () => U): T | U;
        valueOrThrow(error?: Error): T;
        do(patterns?: Partial<MaybePatterns<T, void>>): Maybe<T>;
    }

}
