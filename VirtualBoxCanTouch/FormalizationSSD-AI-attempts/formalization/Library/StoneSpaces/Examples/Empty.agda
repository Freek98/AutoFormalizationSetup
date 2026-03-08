{-# OPTIONS --cubical --guardedness #-}
module formalization.Library.StoneSpaces.Examples.Empty where

open import formalization.Library.StoneSpaces.Spectrum
open import Cubical.Data.Unit

open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import formalization.Library.CountablyPresentedBooleanRings.Examples.Bool
open import formalization.Library.CountablyPresentedBooleanRings.Examples.TrivialBA
open import Cubical.Algebra.BooleanRing.Initial
open import Cubical.Algebra.CommRing

open import Cubical.Foundations.Function
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Prelude
open import formalization.Library.AntiEquivalence

EmptyIsStone : hasStoneStr ⊥
EmptyIsStone .fst = UnitCP
EmptyIsStone .snd = ua (uninhabEquiv (TrivialImpliesSpEmpty.spEmpty UnitCP (isPropUnit* _ _)) λ x → x) 

EmptySpace : StoneSpace
EmptySpace .fst = ⊥
EmptySpace .snd = EmptyIsStone 
