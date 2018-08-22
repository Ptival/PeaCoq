//cf. https://github.com/Microsoft/TypeScript/issues/7352#issuecomment-191547232

import * as TSMonad from 'tsmonad'

declare global {
  const TsMonad = {
    Maybe : TSMonad.Maybe
  }
  type Maybe<T> = TSMonad.Maybe<T>
}
