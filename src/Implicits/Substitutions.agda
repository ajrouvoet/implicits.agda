open import Prelude hiding (lift; Fin′; subst; id)

module Implicits.Substitutions (TC : Set) (_tc≟_ : (a b : TC) → Dec (a ≡ b)) where

import Implicits.Substitutions.Context TC _tc≟_ as CtxSubst
open import Implicits.Substitutions.Term TC _tc≟_

module TypeSubst where
  open import Implicits.Substitutions.Type TC _tc≟_ public

open import Implicits.Substitutions.MetaType TC _tc≟_ public

open TypeSubst public using (_∙_; stp-weaken)
  renaming (_simple/_ to _stp/tp_; _/_ to _tp/tp_; _[/_] to _tp[/tp_]; weaken to tp-weaken)
open TermTypeSubst public using ()
  renaming (_/_ to _tm/tp_; _[/_] to _tm[/tp_]; weaken to tm-weaken)
open TermTermSubst public using ()
  renaming (_/_ to _tm/tm_; _/Var_ to _tm/Var_; _[/_] to _tm[/tm_]; weaken to tmtm-weaken)
open CtxSubst public using (ktx-map; ictx-weaken)
  renaming (_/_ to _ktx/_; _/Var_ to _ktx/Var_; weaken to ktx-weaken)
