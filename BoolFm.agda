module cs2800-challenges.BoolFm where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_; _∨_) renaming (not to !_; _xor_ to _×_)
open import Data.Char.Base using (Char)
open import Data.Char.Properties using (_==_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- my attempt at this can best be described as "unfamiliar with
-- abstraction and idiom in Agda"

-- I don't create an abstraction for `var`, and just use the stdlib's
-- `Char` since there's a lot of annoying name shadowing between
-- types/constructors that just doesn't happen in ACL2s, but does in
-- agda.

data BoolFm1 : Set where
  bool : Bool → BoolFm1
  var : Char → BoolFm1
  not : BoolFm1 → BoolFm1
  or : BoolFm1 → BoolFm1 → BoolFm1
  and : BoolFm1 → BoolFm1 → BoolFm1
  implies : BoolFm1 → BoolFm1 → BoolFm1
  equal : BoolFm1 → BoolFm1 → BoolFm1
  xor : BoolFm1 → BoolFm1 → BoolFm1
  nor : BoolFm1 → BoolFm1 → BoolFm1

data NorFm : Set where
  bool : Bool → NorFm
  var : Char → NorFm
  nor : NorFm → NorFm → NorFm

data NorNCFm : Set where
  var : Char → NorNCFm
  nor : NorNCFm → NorNCFm → NorNCFm

data NorCPFm : Set where
  bool : Bool → NorCPFm
  NorNCCFm→NorCPFm : NorNCFm → NorCPFm

-- defined last to make subtype-like constructors for the other
-- languages
data BoolFm : Set where
  bool : Bool → BoolFm
  var : Char → BoolFm
  not : BoolFm → BoolFm
  or : BoolFm → BoolFm → BoolFm
  and : BoolFm → BoolFm → BoolFm
  implies : BoolFm → BoolFm → BoolFm
  equal : BoolFm → BoolFm → BoolFm
  xor : BoolFm → BoolFm → BoolFm
  nor : BoolFm → BoolFm → BoolFm
  nand : BoolFm → BoolFm → BoolFm
  BoolFm1→BoolFm : BoolFm1 → BoolFm
  NorFm→BoolFm : NorFm → BoolFm
  NorNCFm→BoolFm : NorNCFm → BoolFm
  NorCPFm→BoolFm : NorCPFm → BoolFm
  
-- the way I know to make data types in agda is like this, using
-- constructors. the recursive constructors result in a similar
-- semantics to ACL2s, except each of the clauses in the ACL2s 'or'
-- defdata is given a separate, named constructor. however, ...

-- the subtyping has had to be grouped as additional constructors in
-- `BoolFm`. this style of subtyping is very weird to do in agda and I
-- didn't really like any of my potential solutions. this one I
-- dislike the least since it better mimics the five-under-one
-- structure in ACL2s. agda is obviously much less flexible, and much
-- less 'observation-based' with respect to its typing than ACL2s


-- making this type alias was easier than 'var = Char' since
-- there's no name shadowing
assignment = List Char

lookup : Char → assignment → Bool
lookup v [] = false
lookup v (x ∷ xs) with x == v
... | true = true
... | false = lookup v xs

-- dependently-typed helper functions for duplicate logic in evaluation
boolEval : Bool → Bool
boolEval b = b

varEval : Char → assignment → Bool
varEval v a = lookup v a

notEval : ∀ {Fm : Set} → (Fm → assignment → Bool) → Fm → assignment → Bool
notEval f p a = ! (f p a)

orEval : ∀ {Fm : Set} → (Fm → assignment → Bool) → Fm → Fm → assignment → Bool
orEval f p q a = (f p a) ∨ (f q a)

andEval : ∀ {Fm : Set} → (Fm → assignment → Bool) → Fm → Fm → assignment → Bool
andEval f p q a = (f p a) ∧ (f q a)

impliesEval : ∀ {Fm : Set} → (Fm → assignment → Bool) → Fm → Fm → assignment → Bool
impliesEval f p q a = (! (f p a)) ∨ (f q a)

equalEval : ∀ {Fm : Set} → (Fm → assignment → Bool) → Fm → Fm → assignment → Bool
equalEval f p q a = if f p a then f q a else ! (f q a)

xorEval : ∀ {Fm : Set} → (Fm → assignment → Bool) → Fm → Fm → assignment → Bool
xorEval f p q a = (f p a) × (f q a)

norEval : ∀ {Fm : Set} → (Fm → assignment → Bool) → Fm → Fm → assignment → Bool
norEval f p q a = ! ((f p a) ∨ (f q a))

nandEval : ∀ {Fm : Set} → (Fm → assignment → Bool) → Fm → Fm → assignment → Bool
nandEval f p q a = ! ((f p a) ∧ (f q a))

-- the actual formula evaluation functions. I had to mark these as
-- terminating manually because agda got confused. not sure why

{-# TERMINATING #-}
B1Eval : BoolFm1 → assignment → Bool
B1Eval (bool b) a = boolEval b
B1Eval (var v) a = varEval v a
B1Eval (not p) a = notEval B1Eval p a
B1Eval (or p q) a = orEval B1Eval p q a
B1Eval (and p q) a = andEval B1Eval p q a
B1Eval (implies p q) a = impliesEval B1Eval p q a
B1Eval (equal p q) a = equalEval B1Eval p q a
B1Eval (xor p q) a = xorEval B1Eval p q a
B1Eval (nor p q) a = norEval B1Eval p q a

{-# TERMINATING #-}
NorEval : NorFm → assignment → Bool
NorEval (bool b) a = boolEval b
NorEval (var v) a = varEval v a
NorEval (nor p q) a = norEval NorEval p q a

{-# TERMINATING #-}
NorNCEval : NorNCFm → assignment → Bool
NorNCEval (var v) a = varEval v a
NorNCEval (nor p q) a = norEval NorNCEval p q a

NorCPEval : NorCPFm → assignment → Bool
NorCPEval (bool b) a = boolEval b
NorCPEval (NorNCCFm→NorCPFm p) a = NorNCEval p a

{-# TERMINATING #-}
BfEval : BoolFm → assignment → Bool
BfEval (bool b) a = boolEval b
BfEval (var v) a = varEval v a
BfEval (not p) a = notEval BfEval p a
BfEval (or p q) a = orEval BfEval p q a
BfEval (and p q) a = andEval BfEval p q a
BfEval (implies p q) a = impliesEval BfEval p q a
BfEval (equal p q) a = equalEval BfEval p q a
BfEval (xor p q) a = xorEval BfEval p q a
BfEval (nor p q) a = norEval BfEval p q a
BfEval (nand p q) a = nandEval BfEval p q a
BfEval (BoolFm1→BoolFm p) a = B1Eval p a
BfEval (NorFm→BoolFm p) a = NorEval p a
BfEval (NorNCFm→BoolFm p) a = NorNCEval p a
BfEval (NorCPFm→BoolFm p) a = NorCPEval p a

-- the reality of the type relationship between the languages means
-- that to do full test "coverage" (are these things in agda really
-- tests?) there's a ton of redundancy

_ : BfEval (bool true) [] ≡ true
_ = refl

_ : BfEval (BoolFm1→BoolFm (bool true)) [] ≡ true
_ = refl

_ : BfEval (NorFm→BoolFm (bool true)) [] ≡ true
_ = refl

_ : BfEval (NorCPFm→BoolFm (bool true)) [] ≡ true
_ = refl

-- in the intrest of my own highly valuable time, and since all the
-- logic is abstracted, I am not writing the redundant tests for the
-- subtypes

_ : BfEval (var 'a') ('b' ∷ []) ≡ false
_ = refl

_ : BfEval (not (bool false)) [] ≡ true
_ = refl

_ : BfEval (not (bool true)) [] ≡ false
_ = refl

_ : BfEval (or (var 'a') (var 'b')) ('a' ∷ []) ≡ true
_ = refl

_ : BfEval (or (var 'a') (var 'b')) [] ≡ false
_ = refl

_ : BfEval (and (var 'a') (var 'a')) ('a' ∷ []) ≡ true
_ = refl

_ : BfEval (and (var 'a') (var 'b')) ('a' ∷ []) ≡ false
_ = refl

_ : BfEval (implies (bool true) (bool true)) [] ≡ true
_ = refl

_ : BfEval (implies (bool true) (bool false)) [] ≡ false
_ = refl

_ : BfEval (implies (bool false) (bool true)) [] ≡ true
_ = refl

_ : BfEval (equal (bool true) (bool true)) [] ≡ true
_ = refl

_ : BfEval (equal (bool true) (bool false)) [] ≡ false
_ = refl

_ : BfEval (equal (bool false) (bool false)) [] ≡ true
_ = refl

_ : BfEval (xor (bool false) (bool true)) [] ≡ true
_ = refl

_ : BfEval (xor (bool false) (bool false)) [] ≡ false
_ = refl

_ : BfEval (nor (var 'a') (var 'b')) ('a' ∷ []) ≡ false
_ = refl

_ : BfEval (nor (var 'a') (var 'b')) [] ≡ true
_ = refl

_ : BfEval (nand (var 'a') (var 'a')) ('a' ∷ []) ≡ false
_ = refl

_ : BfEval (nand (var 'a') (var 'b')) ('a' ∷ []) ≡ true
_ = refl

ConstPropNorFm : NorFm → NorCPFm
ConstPropNorFm (bool b) = bool b
ConstPropNorFm (var v) = NorNCCFm→NorCPFm (var v)
ConstPropNorFm (nor p q) with (ConstPropNorFm p) | (ConstPropNorFm q)
... | bool true | _ = bool false
... | _ | (bool true) = bool false
... | bool false | bool false = bool true
... | bool false | NorNCCFm→NorCPFm nq = NorNCCFm→NorCPFm (nor nq nq)
... | NorNCCFm→NorCPFm np | bool false = NorNCCFm→NorCPFm (nor np np)
... | NorNCCFm→NorCPFm np | NorNCCFm→NorCPFm nq = NorNCCFm→NorCPFm (nor np nq)

-- exhaustive boolean cases
_ : ConstPropNorFm (bool true) ≡ (bool true)
_ = refl

_ : ConstPropNorFm (bool false) ≡ (bool false)
_ = refl

-- not going to iterate for every Char literal
_ : ConstPropNorFm (var 'a') ≡ (NorNCCFm→NorCPFm (var 'a'))
_ = refl

-- recursive cases
_ : ConstPropNorFm (nor (bool true) (bool false)) ≡ bool false
_ = refl

_ : ConstPropNorFm (nor (bool false) (bool true)) ≡ bool false
_ = refl

_ : ConstPropNorFm (nor (bool false) (bool false)) ≡ bool true
_ = refl

_ : ConstPropNorFm (nor (bool false) (var 'a')) ≡ NorNCCFm→NorCPFm (nor (var 'a') (var 'a'))
_ = refl

_ : ConstPropNorFm (nor (var 'a') (bool false)) ≡ NorNCCFm→NorCPFm (nor (var 'a') (var 'a'))
_ = refl

_ : ConstPropNorFm (nor (var 'a') (var 'b'))  ≡ NorNCCFm→NorCPFm (nor (var 'a') (var 'b'))
_ = refl

-- one more actually interesting case
_ : ConstPropNorFm (nor (nor (var 'a') (nor (bool true) (bool false))) (nor (var 'b') (bool false))) ≡ NorNCCFm→NorCPFm (nor (nor (var 'a') (var 'a')) (nor (var 'b') (var 'b')))
_ = refl

-- it was fun to use Agda to imitate a more normal language, I've only
-- used it before for working through the https://plfa.github.io/
-- book. it is certainly less interactive and flexible than ACL2s (or
-- basically any language I've ever used), but I like thinking about
-- the types like this. having only done lisp and ruby in class/co-op
-- for the last 10 months, getting back into statically-typed (and
-- dependently-typed) brain is always a fun exercise.

-- other than spending time trolling through the stdlib for basic
-- things (how to compare characters), the most interesting part of
-- this was trying to figure out the most elegant way to do the
-- subtyping and have BfEval work for all the languages defined. and
-- then in my second phase I did the abstraction with the
-- dependently-typed helpers. I'm not completely satisfied with my
-- solution, but short of finding an agda wizard I don't know how to
-- go about improving it since there isn't the bulk of online
-- resources required to learn idioms for specific problems in agda.
