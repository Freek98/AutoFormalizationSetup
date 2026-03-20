

  iterMapComp : (n₀ d₁ d₂ : ℕ) (x : X n₀) →
    PathP (λ i → X (+-assoc d₂ d₁ n₀ i))
      (iterMap (d₁ + n₀) d₂ (iterMap n₀ d₁ x))
      (iterMap n₀ (d₂ + d₁) x)
  iterMapComp n₀ d₁ zero x = refl
  iterMapComp n₀ d₁ (suc d₂) x i = Xmap (iterMapComp n₀ d₁ d₂ x i)

  ιnmcomp : {n m k : ℕ} → (n≤m : n ≤ m) → (m≤k : m ≤ k) → (n≤k : n ≤ k) → (x : X n) →
    ιnm m≤k (ιnm n≤m x) ≡ ιnm n≤k x
  ιnmcomp {n} {m} {k} (d₁ , p₁) (d₂ , p₂) n≤k x =
    cong (subst X p₂) (sym (substCommSlice X (λ a → X (d₂ + a)) (λ a → iterMap a d₂) p₁ z))
    ∙ sym (substComposite X (cong (d₂ +_) p₁) p₂ u)
    ∙ cong (λ q → subst X q u) (isSetℕ _ _ (cong (d₂ +_) p₁ ∙ p₂) (r ∙ s))
    ∙ substComposite X r s u
    ∙ cong (subst X s) (fromPathP (iterMapComp n d₁ d₂ x))
    ∙ ιnmUseProp x
    where
      z = iterMap n d₁ x
      u = iterMap (d₁ + n) d₂ z
      r = +-assoc d₂ d₁ n
      s : (d₂ + d₁) + n ≡ k
      s = sym r ∙ cong (d₂ +_) p₁ ∙ p₂

