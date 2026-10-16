-- | The signature of 'Thena.Core.Convert.convert', for "Thena.Core.Reduce".
--
-- **The layering runs the other way and this one import turns it into a
-- cycle.** @Convert@ is above @Reduce@ (§2.5) and calls 'whnf' at every step;
-- MS8 phase 149's trusted contraction needs the converse, because its side
-- condition is full convertibility and **not** a syntactic approximation of it
-- — his ruling, 2026-10-05. An @.hs-boot@ is how GHC admits that, and **he has
-- no objection to them.**
--
-- **This file is a property of the module layout, not of the design.** A kernel
-- written from scratch would put reduction and conversion in one module and need
-- nothing here, which is why this is a boot file rather than a reshuffle of two
-- modules the rest of the system imports by name.
--
-- Nothing else goes in here. A boot file is a second declaration of whatever it
-- names, so every line added is a line that can come to disagree with
-- @Convert.hs@ — and GHC only checks the ones that are here.
module Thena.Core.Convert where

import Thena.Core.Context (Context)
import Thena.Core.Level (Obligation)
import Thena.Core.Term (Core)
import Thena.Errors (ConversionFailure)
import Thena.Global.Env (GlobalEnv)

convert
  :: GlobalEnv -> Context -> Int -> Core -> Core
  -> (Maybe ConversionFailure, [Obligation], Int)
