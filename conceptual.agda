import Relation.Binary.PropositionalEquality as Eq
open import Data.Product using (∃-syntax; Σ-syntax; _,_; _×_)
open import Level using (0ℓ) renaming (suc to lsuc)
open Eq using (_≡_; refl; trans; sym; cong)
open Eq.≡-Reasoning using (begin_; step-≡; _∎)

-- conceptual mathematics, a first introduction to categories
module conceptual where

  module ArticleI where
    record Category {ℓ} : Set (lsuc ℓ)  where
      infixr 7 _⇒_
      infixl 6 _∘_

      field
        Object : Set ℓ

        -- morphism
        _⇒_ : Object → Object → Set

        -- identity map
        𝟙 : ∀ {A : Object} → A ⇒ A

        -- composition
        _∘_ : ∀ {A B C : Object}
            → B ⇒ C
            → A ⇒ B
            → A ⇒ C

        -- identity map is a right/left identity w.r.t composition
        𝟙-identityˡ : ∀ {A B : Object} (f : A ⇒ B)
                    → 𝟙 ∘ f ≡ f

        𝟙-identityʳ : ∀ {A B : Object} (g : A ⇒ B)
                    → g ∘ 𝟙 ≡ g

        -- composition is associative
        assoc : ∀ {A B C D : Object} (h : C ⇒ D) (g : B ⇒ C) (f : A ⇒ B)
              → h ∘ g ∘ f ≡ h ∘ (g ∘ f)

      variable A B C : Object
      variable e f g h r s : A ⇒ B

  open ArticleI using (Category)

  module ArticleII {ℓ} (𝒞 : Category {ℓ}) where
    open Category 𝒞

    infix 4 _≃_

    -- an isomorphism is a morphism that has an inverse satisfying the following
    -- equational laws
    record Isomorphism (to : A ⇒ B) : Set where
      field
        from : B ⇒ A

        from∘to : from ∘ to ≡ 𝟙

        to∘from : to ∘ from ≡ 𝟙

    open Isomorphism

    -- two objects are isomorphic (A ≃ B) if there exists an isomorphism between
    -- them
    _≃_ : Object → Object → Set
    A ≃ B = Σ[ f ∈ A ⇒ B ] Isomorphism f

    ≃-refl : A ≃ A
    ≃-refl = 𝟙 , iso where
      iso : Isomorphism 𝟙
      from iso = 𝟙
      from∘to iso = 𝟙-identityʳ 𝟙
      to∘from iso = 𝟙-identityʳ 𝟙

    ≃-sym : A ≃ B → B ≃ A
    ≃-sym (f , iso) = from iso , iso′ where
      iso′ : Isomorphism (from iso)
      from iso′ = f
      from∘to iso′ = to∘from iso
      to∘from iso′ = from∘to iso

    ≃-trans : A ≃ B → B ≃ C → A ≃ C
    ≃-trans (f , fiso) (g , giso) = g ∘ f , iso where
      iso : Isomorphism (g ∘ f)
      from iso = from fiso ∘ from giso
      from∘to iso rewrite assoc (from fiso) (from giso) (g ∘ f)
                       | sym (assoc (from giso) g f)
                       | from∘to giso
                       | 𝟙-identityˡ f               = from∘to fiso
      to∘from iso rewrite assoc g f (from fiso ∘ from giso)
                       | sym (assoc f (from fiso) (from giso))
                       | to∘from fiso
                       | 𝟙-identityˡ (from giso)               = to∘from giso

    -- exercise 2: inverses are unique
    inverse-unique : (iso : Isomorphism f) → (iso′ : Isomorphism f) → from iso ≡ from iso′
    inverse-unique {f = f} iso iso′ =
      begin
        from iso
      ≡⟨ sym (𝟙-identityʳ (from iso)) ⟩
        from iso ∘ 𝟙
      ≡⟨ cong (from iso ∘_) (sym (to∘from iso′)) ⟩
        from iso ∘ (f ∘ from iso′)
      ≡⟨ sym (assoc (from iso) f (from iso′)) ⟩
        from iso ∘ f ∘ from iso′
      ≡⟨ cong (_∘ from iso′) (from∘to iso) ⟩
        𝟙 ∘ from iso′
      ≡⟨ 𝟙-identityˡ (from iso′) ⟩
        from iso′
      ∎

    exercise3a : Isomorphism f → f ∘ g ≡ f ∘ h → g ≡ h
    exercise3a {f = f} {g = g} {h = h} iso eq =
      begin
        g
      ≡⟨ sym (𝟙-identityˡ g) ⟩
        𝟙 ∘ g
      ≡⟨ cong (_∘ g) (sym (from∘to iso)) ⟩
        from iso ∘ f ∘ g
      ≡⟨ assoc (from iso) f g ⟩
        from iso ∘ (f ∘ g)
      ≡⟨ cong (from iso ∘_) eq ⟩
        from iso ∘ (f ∘ h)
      ≡⟨ sym (assoc (from iso) f h) ⟩
        from iso ∘ f ∘ h
      ≡⟨ cong (_∘ h) (from∘to iso) ⟩
        𝟙 ∘ h
      ≡⟨ 𝟙-identityˡ h ⟩
        h
      ∎

    exercise3b : Isomorphism f → g ∘ f ≡ h ∘ f → g ≡ h
    exercise3b {f = f} {g = g} {h = h} iso eq =
      begin
        g
      ≡⟨ sym (𝟙-identityʳ g) ⟩
        g ∘ 𝟙
      ≡⟨ cong (g ∘_) (sym (to∘from iso)) ⟩
        g ∘ (f ∘ from iso)
      ≡⟨ sym (assoc g f (from iso)) ⟩
        g ∘ f ∘ from iso
      ≡⟨ cong (_∘ from iso) eq ⟩
        h ∘ f ∘ from iso
      ≡⟨ assoc h f (from iso) ⟩
        h ∘ (f ∘ from iso)
      ≡⟨ cong (h ∘_) (to∘from iso) ⟩
        h ∘ 𝟙
      ≡⟨ 𝟙-identityʳ h ⟩
        h
      ∎

    determination : A ⇒ C → A ⇒ B → B ⇒ C → Set
    determination h f g = g ∘ f ≡ h

    choice : B ⇒ C → A ⇒ C → A ⇒ B → Set
    choice g h f = g ∘ f ≡ h

    retraction : A ⇒ B → B ⇒ A → Set
    retraction f r = determination 𝟙 f r

    section : A ⇒ B → B ⇒ A → Set
    section f s = choice f 𝟙 s

    _surjective-for-maps-from_ : ∀ {A B : Object} → A ⇒ B → Object → Set
    _surjective-for-maps-from_ {B = B} f T =  ∀ (y : T ⇒ B) → ∃[ x ] f ∘ x ≡ y

    prop1 : ∀ {T : Object} {f : A ⇒ B}
          → ∃[ s ] section f s
          → f surjective-for-maps-from T
    prop1 {f = f} (s , sec) y = s ∘ y , lemma where
      lemma : f ∘ (s ∘ y) ≡ y
      lemma rewrite sym (assoc f s y) | sec = 𝟙-identityˡ y

    prop1* : ∀ {T : Object} {f : A ⇒ B}
           → ∃[ r ] retraction f r
           → ∀ (y : A ⇒ T) → ∃[ x ] x ∘ f ≡ y
    prop1* {f = f} (r , ret) y = y ∘ r , lemma where
      lemma : y ∘ r ∘ f ≡ y
      lemma rewrite assoc y r f | ret = 𝟙-identityʳ y

    _injective-for-maps-from_ : ∀ {A B : Object} → A ⇒ B → Object → Set
    _injective-for-maps-from_ {A} f T =
      ∀ (x₁ x₂ : T ⇒ A) → f ∘ x₁ ≡ f ∘ x₂ → x₁ ≡ x₂

    -- proposition 2
    ret→mono : ∀ {T : Object} {f : A ⇒ B}
          → ∃[ r ] retraction f r
          → f injective-for-maps-from T
    ret→mono {f = f} (r , ret) x₁ x₂ eq =
      begin
        x₁
      ≡⟨ sym (𝟙-identityˡ x₁) ⟩
        𝟙 ∘ x₁
      ≡⟨ cong (_∘ x₁) (sym ret) ⟩
        r ∘ f ∘ x₁
      ≡⟨ assoc r f x₁ ⟩
        r ∘ (f ∘ x₁)
      ≡⟨ cong (r ∘_) eq ⟩
        r ∘ (f ∘ x₂)
      ≡⟨ sym (assoc r f x₂) ⟩
        r ∘ f ∘ x₂
      ≡⟨ cong (_∘ x₂) ret ⟩
        𝟙 ∘ x₂
      ≡⟨ 𝟙-identityˡ x₂ ⟩
        x₂
      ∎

    -- left-cancellative morphism
    monomorphism : A ⇒ B → Set ℓ
    monomorphism f = ∀ {T} → f injective-for-maps-from T

    -- right-cancellative morphism
    epimorphism : A ⇒ B → Set ℓ
    epimorphism {B = B} f = ∀ {T} → ∀ (y₁ y₂ : B ⇒ T) → y₁ ∘ f ≡ y₂ ∘ f → y₁ ≡ y₂

    -- proposition 2*
    sec→epi : ∃[ s ] section f s
           → epimorphism f
    sec→epi {f = f} (s , sec) y₁ y₂ eq =
      begin
        y₁
      ≡⟨ sym (𝟙-identityʳ y₁) ⟩
        y₁ ∘ 𝟙
      ≡⟨ cong (y₁ ∘_) (sym sec) ⟩
        y₁ ∘ (f ∘ s)
      ≡⟨ sym (assoc y₁ f s) ⟩
        y₁ ∘ f ∘ s
      ≡⟨ cong (_∘ s) eq ⟩
        y₂ ∘ f ∘ s
      ≡⟨ assoc y₂ f s ⟩
        y₂ ∘ (f ∘ s)
      ≡⟨ cong (y₂ ∘_) sec ⟩
        y₂ ∘ 𝟙
      ≡⟨ 𝟙-identityʳ y₂ ⟩
        y₂
      ∎

    retraction→section : retraction f r → section r f
    retraction→section ret = ret

    section→retraction : section f s → retraction s f
    section→retraction sec = sec

    -- proposition 3
    ret-∘ : ∃[ rf ] retraction f rf → ∃[ rg ] retraction g rg
          → ∃[ r ] retraction (g ∘ f) r
    ret-∘ {f = f} {g = g} (rf , retf) (rg , retg) = rf ∘ rg , lemma where
      lemma : rf ∘ rg ∘ (g ∘ f) ≡ 𝟙
      lemma rewrite assoc rf rg (g ∘ f) | sym (assoc rg g f) | retg
                  | 𝟙-identityˡ f                                   = retf

    -- exercise 8
    sec-∘ : ∃[ sf ] section f sf → ∃[ sg ] section g sg
              → ∃[ s ] section (g ∘ f) s
    sec-∘ {f = f} {g = g} (sf , secf) (sg , secg) = sf ∘ sg , lemma where
      lemma : g ∘ f ∘ (sf ∘ sg) ≡ 𝟙
      lemma rewrite assoc g f (sf ∘ sg) | sym (assoc f sf sg) | secf
                  | 𝟙-identityˡ sg                                   = secg

    idempotent : A ⇒ A → Set
    idempotent e = e ∘ e ≡ e

    exercise9 : retraction f r → e ≡ f ∘ r → idempotent e
    exercise9 {f = f} {r = r} {e = e} ret eq
      rewrite eq | assoc f r (f ∘ r) | sym (assoc r f r) | ret
            | 𝟙-identityˡ r                                    = refl

    -- if an isomorphism has a section and a retraction, these are the same
    -- (this is an alternate proof of the uniqueness of inverses)
    retraction≡section : retraction f r → section f s → r ≡ s
    retraction≡section {f = f} {r = r} {s = s} ret sec =
      begin
        r
      ≡⟨ sym (𝟙-identityʳ r) ⟩
        r ∘ 𝟙
      ≡⟨ cong (r ∘_) (sym sec) ⟩
        r ∘ (f ∘ s)
      ≡⟨ sym (assoc r f s) ⟩
        r ∘ f ∘ s
      ≡⟨ cong (_∘ s) ret ⟩
        𝟙 ∘ s
      ≡⟨ 𝟙-identityˡ s ⟩
        s
      ∎

    -- alternative definition of an isomorphism: a morphism that has both a
    -- retraction as well as a section (which is unique as per theorem above)
    isomorphism : A ⇒ B → Set
    isomorphism f = ∃[ f⁻¹ ] retraction f f⁻¹ × section f f⁻¹

    -- exercise 10
    iso-∘ : Isomorphism f → Isomorphism g → Isomorphism (g ∘ f)
    iso-∘ {f = f} {g = g} fiso giso = iso where
      iso : Isomorphism (g ∘ f)
      from iso = from fiso ∘ from giso
      from∘to iso rewrite assoc (from fiso) (from giso) (g ∘ f)
                       | sym (assoc (from giso) g f)
                       | from∘to giso
                       | 𝟙-identityˡ f                           = from∘to fiso
      to∘from iso rewrite assoc g f (from fiso ∘ from giso)
                       | sym (assoc f (from fiso) (from giso))
                       | to∘from fiso
                       | 𝟙-identityˡ (from giso)               = to∘from giso

    -- an isomorphism + endomorphism
    automorphism : A ⇒ A → Set
    automorphism f = Isomorphism f
