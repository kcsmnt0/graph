open import Data.Graph

module Data.Graph.Path.Search {ℓᵥ ℓₑ} (g : FiniteGraph ℓᵥ ℓₑ) where

open import Data.Graph.Path.Cut g
open import Data.Graph.Path.Finite g
open import Data.Product as Σ
open import Data.Sum as ⊎
open import Data.Vec as Vec
open import Finite
open import Function
open import Level
open import Relation.Binary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (module Dec)
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Negation as ¬

open FiniteGraph g
open IsFinite

pathSearchFrom : ∀ {ℓ} {P : Vertex → Set ℓ} →
  (∀ b → Dec (P b)) → ∀ a → Dec (∃ λ b → P b × ∃ (Path a b))
pathSearchFrom P? a =
  case ∃? (Path≤-finite (size vertexFinite) a) (P? ∘ proj₁) of λ where
    (yes ((_ , _ , _ , p) , pb)) → yes (-, pb , (-, p))
    (no ¬p) → no λ where (_ , pb , _ , p) → ¬p ((-, shortEnoughPath p) , pb)

pathSearchAcyclicFrom : ∀ {ℓ} {P : Vertex → Set ℓ} →
  (∀ b → Dec (P b)) → ∀ a →
  Dec (∃ λ b → P b × ∃₂ λ n (p : Path a b n) → Acyclic p)
pathSearchAcyclicFrom P? a =
  case ∃? (Path≤-finite (size vertexFinite) a) (P? ∘ proj₁) of λ where
    (yes ((_ , _ , _ , p) , pb)) →
      let (x , x≤n , p′) , ¬r′ = acyclicPath p in
        yes (-, pb , (-, (p′ , ¬r′)))
    (no ¬p) → no λ where (_ , pb , _ , p , r) → ¬p ((-, shortEnoughPath p) , pb)

pathSearchBetween : ∀ a b → Dec (∃ (Path a b))
pathSearchBetween a b =
  case pathSearchFrom (decEqVertex b) a of λ where
    (yes (_ , refl , p)) → yes p
    (no ¬p) → no λ where (n , p) → ¬p (-, refl , -, p)

searchFrom : ∀ {ℓ} {P : Vertex → Set ℓ} →
  (∀ b → Dec (P b)) →
  ∀ a → Dec (∃ λ b → P b × Star Edge a b)
searchFrom P? a =
  Dec.map′
    (Σ.map₂ (Σ.map₂ (toStar ∘ proj₂)))
    (Σ.map₂ (Σ.map₂ (-,_ ∘ fromStar)))
    (pathSearchFrom P? a)

searchBetween : ∀ a b → Dec (Star Edge a b)
searchBetween a b = Dec.map′ (toStar ∘ proj₂) (-,_ ∘ fromStar) (pathSearchBetween a b)

module _
  {ℓ ℓ≈ ℓ<}
  {P : Vertex → Set ℓ} (P? : ∀ a → Dec (P a))
  {_≈_ : ∀ {a} → Rel (∃ (Star Edge a)) ℓ≈}
  {_<_ : ∀ {a} → Rel (∃ (Star Edge a)) ℓ<}
  (<-po : ∀ {a} → IsDecStrictPartialOrder (_≈_ {a}) _<_)
  where

  record MaximalPath a : Set (ℓ ⊔ ℓᵥ ⊔ ℓₑ ⊔ ℓ<) where
    field
      destination : Vertex
      predicate : P destination
      path : Star Edge a destination
      acyclic : Acyclic (fromStar path)
      isMax : ∀
        {b} (p : Star Edge a b) (pb : P b) → Acyclic (fromStar p) →
        ¬ ((-, path) < (-, p))

  searchMaximalFrom : ∀ a → Dec (MaximalPath a)
  searchMaximalFrom a =
    case max of λ where
      (inj₁ ¬p) →
        no λ mp →
          let open MaximalPath mp in
            ¬p ((-, path , fromWitness acyclic) , fromWitness predicate)

      (inj₂ (((b , p , acp) , pb) , isMax)) →
        yes record
          { destination = b
          ; predicate = toWitness pb
          ; path = p
          ; acyclic = toWitness acp
          ; isMax = λ q pb acq → isMax ((-, q , fromWitness acq) , fromWitness pb)
          }
    where
      module DPO = IsDecStrictPartialOrder <-po

      _≈′_ = _≈_ on λ where ((b , p , acp) , pb) → b , p
      _<′_ = _<_ on λ where ((b , p , acp) , pb) → b , p

      <′-IsDecStrictPartialOrder : IsDecStrictPartialOrder _≈′_ _<′_
      <′-IsDecStrictPartialOrder = record
        { isStrictPartialOrder = record
          { isEquivalence = record
            { refl = IsEquivalence.refl DPO.isEquivalence
            ; sym = IsEquivalence.sym DPO.isEquivalence
            ; trans = IsEquivalence.trans DPO.isEquivalence
            }
          ; irrefl = DPO.irrefl
          ; trans = DPO.trans
          ; <-resp-≈ = proj₁ DPO.<-resp-≈ , proj₂ DPO.<-resp-≈
          }
        ; _≟_ = λ _ _ → _ DPO.≟ _
        ; _<?_ = λ _ _ → _ DPO.<? _
        }

      acyclicPaths = IsFinite.filter (AcyclicStar-finite a) (P? ∘ proj₁)

      open Ordered acyclicPaths <′-IsDecStrictPartialOrder
