import Relation.Binary.PropositionalEquality as Eq
open import Data.Product using (∃-syntax; Σ-syntax; _,_)
open Eq using (_≡_; refl; trans; sym; cong)
open Eq.≡-Reasoning using (begin_; step-≡; _∎)

-- conceptual mathematics, a first introduction to categories
module conceptual where

  module ArticleI where
    record Category : Set₁ where
      infixr 7 _⟶_
      infixl 6 _∘_

      field
        Object : Set

        _⟶_ : Object → Object → Set

        𝐼 : ∀ {A : Object} → A ⟶ A

        _∘_ : ∀ {A B C : Object}
            → B ⟶ C
            → A ⟶ B
            → A ⟶ C

        𝐼-identityˡ : ∀ {A B : Object} (f : A ⟶ B)
                    → 𝐼 ∘ f ≡ f

        𝐼-identityʳ : ∀ {A B : Object} (g : A ⟶ B)
                    → g ∘ 𝐼 ≡ g

        assoc : ∀ {A B C D : Object} (h : C ⟶ D) (g : B ⟶ C) (f : A ⟶ B)
              → h ∘ g ∘ f ≡ h ∘ (g ∘ f)

      variable A B C : Object
      variable e f g h r s : A ⟶ B

  open ArticleI using (Category)

  module ArticleII (𝒞 : Category) where
    open Category 𝒞
    record Isomorphism (f : A ⟶ B) : Set where
      field
        inv : B ⟶ A

        inv-𝐼ˡ : inv ∘ f ≡ 𝐼

        inv-𝐼ʳ : f ∘ inv ≡ 𝐼

    open Isomorphism

    isomorphic : Object → Object → Set
    isomorphic A B = Σ[ f ∈ A ⟶ B ] Isomorphism f

    isomorphic-refl : isomorphic A A
    isomorphic-refl = 𝐼 , iso where
      iso : Isomorphism 𝐼
      inv iso = 𝐼
      inv-𝐼ˡ iso = 𝐼-identityʳ 𝐼
      inv-𝐼ʳ iso = 𝐼-identityʳ 𝐼

    isomorphic-sym : isomorphic A B → isomorphic B A
    isomorphic-sym (f , iso) = inv iso , iso′ where
      iso′ : Isomorphism (inv iso)
      inv iso′ = f
      inv-𝐼ˡ iso′ = inv-𝐼ʳ iso
      inv-𝐼ʳ iso′ = inv-𝐼ˡ iso

    isomorphic-trans : isomorphic A B → isomorphic B C → isomorphic A C
    isomorphic-trans (f , fiso) (g , giso) = g ∘ f , iso where
      iso : Isomorphism (g ∘ f)
      inv iso = inv fiso ∘ inv giso
      inv-𝐼ˡ iso rewrite assoc (inv fiso) (inv giso) (g ∘ f)
                       | sym (assoc (inv giso) g f)
                       | inv-𝐼ˡ giso
                       | 𝐼-identityˡ f                       = inv-𝐼ˡ fiso
      inv-𝐼ʳ iso rewrite assoc g f (inv fiso ∘ inv giso)
                       | sym (assoc f (inv fiso) (inv giso))
                       | inv-𝐼ʳ fiso
                       | 𝐼-identityˡ (inv giso)              = inv-𝐼ʳ giso

    exercise3a : Isomorphism f → f ∘ g ≡ f ∘ h → g ≡ h
    exercise3a {f = f} {g = g} {h = h} iso eq =
      begin
        g
      ≡⟨ sym (𝐼-identityˡ g) ⟩
        𝐼 ∘ g
      ≡⟨ cong (_∘ g) (sym (inv-𝐼ˡ iso)) ⟩
        inv iso ∘ f ∘ g
      ≡⟨ assoc (inv iso) f g ⟩
        inv iso ∘ (f ∘ g)
      ≡⟨ cong (inv iso ∘_) eq ⟩
        inv iso ∘ (f ∘ h)
      ≡⟨ sym (assoc (inv iso) f h) ⟩
        inv iso ∘ f ∘ h
      ≡⟨ cong (_∘ h) (inv-𝐼ˡ iso) ⟩
        𝐼 ∘ h
      ≡⟨ 𝐼-identityˡ h ⟩
        h
      ∎

    exercise3b : Isomorphism f → g ∘ f ≡ h ∘ f → g ≡ h
    exercise3b {f = f} {g = g} {h = h} iso eq =
      begin
        g
      ≡⟨ sym (𝐼-identityʳ g) ⟩
        g ∘ 𝐼
      ≡⟨ cong (g ∘_) (sym (inv-𝐼ʳ iso)) ⟩
        g ∘ (f ∘ inv iso)
      ≡⟨ sym (assoc g f (inv iso)) ⟩
        g ∘ f ∘ inv iso
      ≡⟨ cong (_∘ inv iso) eq ⟩
        h ∘ f ∘ inv iso
      ≡⟨ assoc h f (inv iso) ⟩
        h ∘ (f ∘ inv iso)
      ≡⟨ cong (h ∘_) (inv-𝐼ʳ iso) ⟩
        h ∘ 𝐼
      ≡⟨ 𝐼-identityʳ h ⟩
        h
      ∎

    determination : A ⟶ C → A ⟶ B → B ⟶ C → Set
    determination h f g = g ∘ f ≡ h

    choice : B ⟶ C → A ⟶ C → A ⟶ B → Set
    choice g h f = g ∘ f ≡ h

    retraction : A ⟶ B → B ⟶ A → Set
    retraction f r = determination 𝐼 f r

    section : A ⟶ B → B ⟶ A → Set
    section f s = choice f 𝐼 s

    _surjective-for-maps-from_ : ∀ {A B : Object} → A ⟶ B → Object → Set
    _surjective-for-maps-from_ {B = B} f T =  ∀ (y : T ⟶ B) → ∃[ x ] f ∘ x ≡ y

    prop1 : ∀ {T : Object} {f : A ⟶ B}
          → ∃[ s ] section f s
          → f surjective-for-maps-from T
    prop1 {f = f} (s , sec) y = s ∘ y , lemma where
      lemma : f ∘ (s ∘ y) ≡ y
      lemma rewrite sym (assoc f s y) | sec = 𝐼-identityˡ y

    prop1* : ∀ {T : Object} {f : A ⟶ B}
           → ∃[ r ] retraction f r
           → ∀ (y : A ⟶ T) → ∃[ x ] x ∘ f ≡ y
    prop1* {f = f} (r , ret) y = y ∘ r , lemma where
      lemma : y ∘ r ∘ f ≡ y
      lemma rewrite assoc y r f | ret = 𝐼-identityʳ y

    _injective-for-maps-from_ : ∀ {A B : Object} → A ⟶ B → Object → Set
    _injective-for-maps-from_ {A} f T =
      ∀ (x₁ x₂ : T ⟶ A) → f ∘ x₁ ≡ f ∘ x₂ → x₁ ≡ x₂

    prop2 : ∀ {T : Object} {f : A ⟶ B}
          → ∃[ r ] retraction f r
          → f injective-for-maps-from T
    prop2 {f = f} (r , ret) x₁ x₂ eq =
      begin
        x₁
      ≡⟨ sym (𝐼-identityˡ x₁) ⟩
        𝐼 ∘ x₁
      ≡⟨ cong (_∘ x₁) (sym ret) ⟩
        r ∘ f ∘ x₁
      ≡⟨ assoc r f x₁ ⟩
        r ∘ (f ∘ x₁)
      ≡⟨ cong (r ∘_) eq ⟩
        r ∘ (f ∘ x₂)
      ≡⟨ sym (assoc r f x₂) ⟩
        r ∘ f ∘ x₂
      ≡⟨ cong (_∘ x₂) ret ⟩
        𝐼 ∘ x₂
      ≡⟨ 𝐼-identityˡ x₂ ⟩
        x₂
      ∎

    monomorphism : A ⟶ B → Set
    monomorphism f = ∀ {T} → f injective-for-maps-from T

    epimorphism : A ⟶ B → Set
    epimorphism {B = B} f = ∀ {T} → ∀ (y₁ y₂ : B ⟶ T) → y₁ ∘ f ≡ y₂ ∘ f → y₁ ≡ y₂

    prop2* : ∃[ s ] section f s
           → epimorphism f
    prop2* {f = f} (s , sec) y₁ y₂ eq =
      begin
        y₁
      ≡⟨ sym (𝐼-identityʳ y₁) ⟩
        y₁ ∘ 𝐼
      ≡⟨ cong (y₁ ∘_) (sym sec) ⟩
        y₁ ∘ (f ∘ s)
      ≡⟨ sym (assoc y₁ f s) ⟩
        y₁ ∘ f ∘ s
      ≡⟨ cong (_∘ s) eq ⟩
        y₂ ∘ f ∘ s
      ≡⟨ assoc y₂ f s ⟩
        y₂ ∘ (f ∘ s)
      ≡⟨ cong (y₂ ∘_) sec ⟩
        y₂ ∘ 𝐼
      ≡⟨ 𝐼-identityʳ y₂ ⟩
        y₂
      ∎

    retraction→section : retraction f r → section r f
    retraction→section rec = rec

    section→retraction : section f s → retraction s f
    section→retraction sec = sec

    prop3 : ∃[ rf ] retraction f rf → ∃[ rg ] retraction g rg
          → ∃[ r ] retraction (g ∘ f) r
    prop3 {f = f} {g = g} (rf , recf) (rg , recg) = rf ∘ rg , lemma where
      lemma : rf ∘ rg ∘ (g ∘ f) ≡ 𝐼
      lemma rewrite assoc rf rg (g ∘ f) | sym (assoc rg g f) | recg
                  | 𝐼-identityˡ f                                   = recf

    exercise8 : ∃[ sf ] section f sf → ∃[ sg ] section g sg
              → ∃[ s ] section (g ∘ f) s
    exercise8 {f = f} {g = g} (sf , secf) (sg , secg) = sf ∘ sg , lemma where
      lemma : g ∘ f ∘ (sf ∘ sg) ≡ 𝐼
      lemma rewrite assoc g f (sf ∘ sg) | sym (assoc f sf sg) | secf
                  | 𝐼-identityˡ sg                                   = secg

    idempotent : A ⟶ A → Set
    idempotent e = e ∘ e ≡ e

    exercise9 : retraction f r → e ≡ f ∘ r → idempotent e
    exercise9 {f = f} {r = r} {e = e} rec eq
      rewrite eq | assoc f r (f ∘ r) | sym (assoc r f r) | rec
            | 𝐼-identityˡ r                                    = refl

    inverse-unique : retraction f r → section f s → r ≡ s
    inverse-unique {f = f} {r = r} {s = s} rec sec =
      begin
        r
      ≡⟨ sym (𝐼-identityʳ r) ⟩
        r ∘ 𝐼
      ≡⟨ cong (r ∘_) (sym sec) ⟩
        r ∘ (f ∘ s)
      ≡⟨ sym (assoc r f s) ⟩
        r ∘ f ∘ s
      ≡⟨ cong (_∘ s) rec ⟩
        𝐼 ∘ s
      ≡⟨ 𝐼-identityˡ s ⟩
        s
      ∎

    exercise10 : Isomorphism f → Isomorphism g → Isomorphism (g ∘ f)
    exercise10 {f = f} {g = g} fiso giso = iso where
      iso : Isomorphism (g ∘ f)
      inv iso = inv fiso ∘ inv giso
      inv-𝐼ˡ iso rewrite assoc (inv fiso) (inv giso) (g ∘ f)
                       | sym (assoc (inv giso) g f)
                       | inv-𝐼ˡ giso
                       | 𝐼-identityˡ f                       = inv-𝐼ˡ fiso
      inv-𝐼ʳ iso rewrite assoc g f (inv fiso ∘ inv giso)
                       | sym (assoc f (inv fiso) (inv giso))
                       | inv-𝐼ʳ fiso
                       | 𝐼-identityˡ (inv giso)              = inv-𝐼ʳ giso
