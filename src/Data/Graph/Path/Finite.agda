open import Data.Graph

module Data.Graph.Path.Finite {ℓᵥ ℓₑ} (g : FiniteGraph ℓᵥ ℓₑ) where

open import Data.Bool as Bool using (Bool; true; false)
open import Data.Graph.Path.Cut g hiding (_∈_)
open import Data.List as List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties hiding (finite)
open import Data.List.Effectful as ListCat
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties as ℕ
open import Data.Product as Σ
open import Data.Unit using (⊤; tt)
open import Data.Sum as ⊎
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Effect.Monad
import Level as ℓ
open import Finite
open import Function using (id; _∘_; _∋_; case_of_; _$_; LeftInverse)
open import Function.Equality using (Π)
open import Function.Equivalence using (Equivalence)
open import Function.Inverse using (Inverse)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive hiding (_>>=_)
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Binary.HeterogeneousEquality as ≅
open import Relation.Nullary hiding (module Dec)
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Negation

open Π using (_⟨$⟩_)
open Function.Equivalence.Equivalence using (to; from)
open FiniteGraph g
open Function.Inverse.Inverse using (to; from)
open IsFinite
open RawMonad {ℓᵥ ℓ.⊔ ℓₑ} ListCat.monad

isubst : ∀ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁}
  (A : I → Set ℓ₂) (B : ∀ {k} → A k → Set ℓ₃)
  {i j : I} {x : A i} {y : A j} →
  i ≡ j → x ≅ y →
  B x → B y
isubst A B refl refl = id

True-unique : ∀ {ℓ} {A : Set ℓ} (A? : Dec A) (x y : True A?) → x ≡ y
True-unique A? x y with A?
True-unique A? tt tt | yes a = refl
True-unique A? () y | no ¬a

True-unique-≅ : ∀
  {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
  (A? : Dec A) (B? : Dec B)
  (x : True A?) (y : True B?) →
  x ≅ y
True-unique-≅ A? B? x y with A? | B?
True-unique-≅ A? B? tt tt | yes a | yes b = refl
True-unique-≅ A? B? x () | _ | no ¬b
True-unique-≅ A? B? () y | no ¬a | _

∃-≅ : ∀
  {ℓ₁ ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂}
  {x y : A} {p : P x} {q : P y} →
  x ≡ y → p ≅ q → (∃ P ∋ (x , p)) ≡ (y , q)
∃-≅ refl refl = refl

nexts : ∀ {a b n} → Path a b n → List (∃ λ b → Path a b (suc n))
nexts {a} {b} p = List.map (λ where (_ , e) → -, p ∷ʳ e) (elements (edgeFinite {b}))

∈-nexts : ∀ {a c n} →
  (pf : IsFinite (∃ λ b → Path a b n)) →
  (p : Path a c (suc n)) →
  (c , p) ∈ (elements pf >>= (nexts ∘ proj₂))
∈-nexts pf p =
  case unsnoc p of λ where
    (_ , p′ , e′ , refl) →
      to >>=-∈↔ ⟨$⟩
        (-,
          membership pf (-, p′) ,
          ∈-map⁺ _ (membership edgeFinite (-, e′)))

Path-finite : ∀ n a → IsFinite (∃ λ b → Path a b n)
Path-finite zero a = finite List.[ -, [] ] λ where (_ , []) → here refl
Path-finite (suc n) a =
  let pf = Path-finite n a in
    finite (elements pf >>= (nexts ∘ proj₂)) (∈-nexts pf ∘ proj₂)

≤-top? : ∀ {x y} → x ≤ suc y → x ≤ y ⊎ x ≡ suc y
≤-top? z≤n = inj₁ z≤n
≤-top? {y = zero} (s≤s z≤n) = inj₂ refl
≤-top? {y = suc y} (s≤s p) =
  case ≤-top? p of λ where
    (inj₁ le) → inj₁ (s≤s le)
    (inj₂ refl) → inj₂ refl

Path≤-finite : ∀ n a → IsFinite (∃ λ b → Path≤ a b n)
Path≤-finite zero a = finite List.[ -, -, z≤n , [] ] λ where (_ , _ , z≤n , []) → here refl
Path≤-finite (suc n) a =
  let
    finite xs elem = Path≤-finite n a
    finite xs′ elem′ = Path-finite (suc n) a
  in
    finite
      (List.map (Σ.map₂ (Σ.map₂ (Σ.map₁ m≤n⇒m≤1+n))) xs List.++
        List.map (Σ.map₂ (_,_ (suc n) ∘ _,_ ≤-refl)) xs′)
      λ where
        (b , m , le , p) → case ≤-top? le of λ where
          (inj₁ le′) →
            to ++↔ ⟨$⟩
              inj₁
                (to (map-∈↔ _) ⟨$⟩
                  (-, elem (b , m , le′ , p) ,
                    ≡.cong (λ q → b , m , q , p) (ℕ.≤-irrelevant le (m≤n⇒m≤1+n le′))))
          (inj₂ refl) →
            to (++↔ {xs = List.map _ xs}) ⟨$⟩
              inj₂
                (to (map-∈↔ _) ⟨$⟩
                  (-, elem′ (-, p) ,
                    ≡.cong (λ q → b , m , q , p) (≤-irrelevant le (s≤s ≤-refl))))

AcyclicPath-finite : ∀ a → IsFinite (∃₂ λ b n → ∃ λ (p : Path a b n) → True (acyclic? p))
AcyclicPath-finite a =
  via-left-inverse (IsFinite.filter (Path≤-finite (size vertexFinite) a) _) $
    Function.mk↩
      {to = λ where ((b , n , le , p) , acp) → b , n , p , acp}
      {from = λ where (b , n , p , acp) → (b , n , acyclic-length-≤ p (toWitness acp) , p) , acp}
      λ where (b , n , p , acp) → refl

AcyclicStar : Vertex → Vertex → Set _
AcyclicStar a b = ∃ λ (p : Star Edge a b) → True (acyclic? (fromStar p))

AcyclicStar-finite : ∀ a → IsFinite (∃ (AcyclicStar a))
AcyclicStar-finite a =
  via-left-inverse (AcyclicPath-finite a) $
    Function.mk↩
      {to = λ where
        (b , n , p , acp) →
          b , toStar p ,
            isubst (Path a b) (True ∘ acyclic?)
              (starLength-toStar p) (fromStar-toStar p)
              acp}
      {from = λ where
        (b , p , acp) →
          b , starLength p , fromStar p , acp}
      λ where
        (b , p , acp) →
          ≡.cong (b ,_) $
            ∃-≅
              (≡.sym (toStar-fromStar p))
              (True-unique-≅ _ _ _ _)
