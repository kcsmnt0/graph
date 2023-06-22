open import Data.Graph

module Data.Graph.Path.Cut {ℓᵥ ℓₑ} (g : FiniteGraph ℓᵥ ℓₑ) where

open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Fin.Properties as Fin using (pigeonhole)
open import Data.List as List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Membership.Propositional as ∈L renaming (_∈_ to _∈L_)
open import Data.Nat as ℕ
open import Data.Nat.Induction
open import Data.Nat.Properties as ℕ
open import Data.Product as Σ
open import Data.Sum as ⊎
open import Finite
import Finite.Pigeonhole
open import Function
open import Induction.WellFounded
import Level as ℓ
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Reasoning.Preorder ≤-preorder
open import Relation.Nullary hiding (module Dec)
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Negation

open FiniteGraph g
open IsFinite

infix 3 _∈_
data _∈_ x : ∀ {a b n} → Path a b n → Set ℓᵥ where
  here : ∀ {b c n y} {e : Edge y b} {p : Path b c n} → x ≡ y → x ∈ e ∷ p
  there : ∀ {a b c n} {e : Edge a b} {p : Path b c n} → x ∈ p → x ∈ e ∷ p

infix 3 _∈?_
_∈?_ : ∀ {a b n} x (p : Path a b n) → Dec (x ∈ p)
x ∈? [] = no λ ()
_∈?_ {a} x (e ∷ p) =
  case decEqVertex a x of λ where
    (yes refl) → yes (here refl)
    (no a≢x) →
      case x ∈? p of λ where
        (yes i) → yes (there i)
        (no ¬i) → no λ where
          (here x≡a) → contradiction (sym x≡a) a≢x
          (there i) → contradiction i ¬i

index : ∀ {a b x n} {p : Path a b n} → x ∈ p → Fin n
index (here refl) = zero
index (there i) = suc (index i)

lookup : ∀ {a b n} → Path a b n → Fin n → Vertex
lookup {a} (e ∷ p) zero = a
lookup (e ∷ p) (suc i) = lookup p i

∈-lookup : ∀ {a b n} {p : Path a b n} (i : Fin n) → lookup p i ∈ p
∈-lookup {p = []} ()
∈-lookup {p = e ∷ p} zero = here refl
∈-lookup {p = e ∷ p} (suc i) = there (∈-lookup i)

finiteIndex : ∀ {a b n} (p : Path a b n) → Fin n → Fin (size vertexFinite)
finiteIndex p = Any.index ∘ membership vertexFinite ∘ lookup p

prefixLength : ∀ {a b x n} {p : Path a b n} → x ∈ p → ℕ
prefixLength (here refl) = zero
prefixLength (there i) = suc (prefixLength i)

suffixLength : ∀ {a b x n} {p : Path a b n} → x ∈ p → ℕ
suffixLength {n = n} (here refl) = n
suffixLength (there i) = suffixLength i

split : ∀ {a b x n} {p : Path a b n}
  (i : x ∈ p) →
  Path a x (prefixLength i) × Path x b (suffixLength i)
split {p = p} (here refl) = [] , p
split {p = e ∷ p} (there i) = Σ.map₁ (e ∷_) (split i)

prefix : ∀ {a b x n} {p : Path a b n} (i : x ∈ p) → Path a x (prefixLength i)
prefix = proj₁ ∘ split

suffix : ∀ {a b x n} {p : Path a b n} (i : x ∈ p) → Path x b (suffixLength i)
suffix = proj₂ ∘ split

splitLengthsAddUp : ∀ {a b x n} {p : Path a b n}
  (i : x ∈ p) →
  n ≡ prefixLength i + suffixLength i
splitLengthsAddUp (here refl) = refl
splitLengthsAddUp (there i) = cong suc (splitLengthsAddUp i)

data Repeats : ∀ {a b n} → Path a b n → Set ℓᵥ where
  here : ∀ {a b c n} {e : Edge a b} {p : Path b c n} → a ∈ p → Repeats (e ∷ p)
  there : ∀ {a b c n} {e : Edge a b} {p : Path b c n} → Repeats p → Repeats (e ∷ p)

repeats? : ∀ {a b n} (p : Path a b n) → Dec (Repeats p)
repeats? [] = no λ ()
repeats? {a} (e ∷ p) =
  case a ∈? p of λ where
    (yes i) → yes (here i)
    (no ¬i) →
      case repeats? p of λ where
        (yes r) → yes (there r)
        (no ¬r) →
          no λ where
            (here i) → contradiction i ¬i
            (there r) → contradiction r ¬r

Acyclic : ∀ {a b n} → Path a b n → Set _
Acyclic p = ¬ Repeats p

acyclic? : ∀ {a b n} (p : Path a b n) → Dec (Acyclic p)
acyclic? = ¬? ∘ repeats?

data Segmented a b : ℕ → Set (ℓᵥ ℓ.⊔ ℓₑ) where
  _◄_◄_ : ∀ {x m n l} →
    Path a x m →
    Path x x (suc n) →
    Path x b l →
    Segmented a b (m + suc n + l)

segment : ∀ {a b n} {p : Path a b n} → Repeats p → Segmented a b n
segment {p = []} ()
segment {p = e ∷ p} (here i) rewrite splitLengthsAddUp i = [] ◄ e ∷ prefix i ◄ suffix i
segment {p = e ∷ p} (there r) = case segment r of λ where (p₁ ◄ p₂ ◄ p₃) → (e ∷ p₁) ◄ p₂ ◄ p₃

cutLoop< : ∀ {a b n} {p : Path a b n} → Repeats p → Path< a b n
cutLoop< r = case segment r of λ where (_◄_◄_ {m = m} p₁ p₂ p₃) → -, lengthLem m , p₁ ++ p₃
  where
    lengthLem : ∀ x {y z} → suc (x + z) ≤ x + suc y + z
    lengthLem zero = s≤s (m≤n+m _ _)
    lengthLem (suc x) = s≤s (lengthLem x)

indicesLoop : ∀ {a b n i j} {p : Path a b n} → i ≢ j → lookup p i ≡ lookup p j → Repeats p
indicesLoop {i = zero} {zero} {e ∷ p} z≢z eq = contradiction refl z≢z
indicesLoop {i = zero} {suc j} {e ∷ p} _ refl = here (∈-lookup j)
indicesLoop {i = suc i} {zero} {e ∷ p} _ refl = here (∈-lookup i)
indicesLoop {i = suc i} {suc j} {e ∷ p} si≢sj eq = there (indicesLoop (si≢sj ∘ cong suc) eq)

findLoop : ∀ {a b n} (p : Path a b n) → n > size vertexFinite → Repeats p
findLoop p gt =
  let i , j , i<j , eq = pigeonhole gt (finiteIndex p) in
    indicesLoop (Fin.<⇒≢ i<j) (indexOf-injective vertexFinite eq)

acyclic-length-≤ : ∀ {a b n} (p : Path a b n) → Acyclic p → n ≤ size vertexFinite
acyclic-length-≤ {n = n} p ¬r =
  case n ≤? size vertexFinite of λ where
    (yes le) → le
    (no ¬le) → contradiction (findLoop p (≰⇒> ¬le)) ¬r

shortenPath : ∀ {a b n} → Path a b n → n > size vertexFinite → Path< a b n
shortenPath p = cutLoop< ∘ findLoop p

shortenPathEnough : ∀ {a b n}
  (p : Path a b n) →
  n > size vertexFinite →
  Path≤ a b (size vertexFinite)
shortenPathEnough = <-rec _ wfRec _
  where
    wfRec =
      λ n rec p gt →
        let n′ , le , p′ = shortenPath p gt in
          case size vertexFinite <? n′ of λ where
            (yes n′>v) → rec _ le p′ n′>v
            (no n′≯v) → -, ≮⇒≥ n′≯v , p′

shortEnoughPath : ∀ {a b n} (p : Path a b n) → Path≤ a b (size vertexFinite)
shortEnoughPath {n = n} p =
  case size vertexFinite <? n of λ where
    (yes n>v) → shortenPathEnough p n>v
    (no n≯v) → -, ≮⇒≥ n≯v , p

cutAllLoops : ∀ {a b n} →
  (p : Path a b n) →
  Repeats p →
  ∃ λ (p : Path≤ a b n) → Acyclic (proj₂ (proj₂ p))
cutAllLoops = <-rec _ wfRec _
  where
    wfRec = λ x rec p r →
      case cutLoop< r of λ where
        (n′ , lt , p′) →
          case repeats? p′ of λ where
            (yes r) →
              case rec _ lt p′ r of λ where
                ((n′′ , le′′ , p′′) , ¬r′′) →
                  (n′′ , ≤-trans le′′ (<⇒≤ lt) , p′′) , ¬r′′
            (no ¬r) → (n′ , <⇒≤ lt , p′) , ¬r

acyclicPath : ∀ {a b n} →
  (p : Path a b n) →
  ∃ λ (p : Path≤ a b n) → Acyclic (proj₂ (proj₂ p))
acyclicPath p =
  case repeats? p of λ where
    (yes r) → cutAllLoops p r
    (no ¬r) → (-, ≤-refl , p) , ¬r

minimalPath : ∀ {a b n} →
  Path a b n →
  ∃ λ (p : Path≤ a b (size vertexFinite)) → Acyclic (proj₂ (proj₂ p))
minimalPath p =
  let
    x , x≤max , p′ = shortEnoughPath p
    (y , y≤x , p′′) , ¬r = acyclicPath p′
  in
    (y , ≤-trans y≤x x≤max , p′′) , ¬r
