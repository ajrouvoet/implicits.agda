open import Prelude

module Implicits.Substitutions where

import Implicits.Substitutions.Context as CtxSubst
open import Implicits.Substitutions.Term

module TypeSubst where
  open import Implicits.Substitutions.Type public

open import Implicits.Substitutions.MetaType public

open TypeSubst public using (_∙_; stp-weaken)
  renaming (_simple/_ to _stp/tp_; _/_ to _tp/tp_; _[/_] to _tp[/tp_]; weaken to tp-weaken)
open TermTypeSubst public using ()
  renaming (_/_ to _tm/tp_; _[/_] to _tm[/tp_]; weaken to tm-weaken)
open TermTermSubst public using ()
  renaming (_/_ to _tm/tm_; _/Var_ to _tm/Var_; _[/_] to _tm[/tm_]; weaken to tmtm-weaken)
open CtxSubst public using (ktx-map; ictx-weaken; ctx-weaken)
  renaming (_/_ to _ktx/_; _/Var_ to _ktx/Var_; weaken to ktx-weaken)
