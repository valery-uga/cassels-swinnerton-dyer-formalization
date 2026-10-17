import PfaffianDescent.ProjectivePositiveTwist

/-!
# Addition of positive projective twists

Homogeneous fractions multiply to give the canonical map
`O(m) ⊗ O(n) → O(m+n)`.
-/

noncomputable section

namespace PfaffianDescent

open scoped DirectSum Pointwise
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

universe u

namespace ProjectiveNegativeTwist

variable {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

local notation "X" => ProjectiveSpectrum.top 𝒜

/-- Two fixed positive fractions of degrees `m` and `n` multiply to a fixed
positive fraction of degree `m+n`. -/
theorem isPositiveSectionFraction_mul_positiveSectionFraction
    (m n : ℕ) {U : Opens X} {f g : ∀ x : U, PositiveFiber 𝒜 x.1}
    (hf : IsPositiveSectionFraction 𝒜 m f)
    (hg : IsPositiveSectionFraction 𝒜 n g) :
    IsPositiveSectionFraction 𝒜 (m + n) (fun x ↦ f x * g x) := by
  rcases hf with rfl | ⟨i, a, b, hb, hf⟩
  · exact Or.inl (funext fun x ↦ zero_mul (g x))
  rcases hg with rfl | ⟨j, c, d, hd, hg⟩
  · exact Or.inl (funext fun x ↦ mul_zero (f x))
  right
  let k := i + j
  let num : 𝒜 ((m + n) + k) := ⟨(a : A) * c, by
    have h : (a : A) * c ∈ 𝒜 ((m + i) + (n + j)) :=
      mul_mem_graded a.2 c.2
    rw [show (m + i) + (n + j) = (m + n) + k by
      dsimp [k]
      omega] at h
    exact h⟩
  let den : 𝒜 k := ⟨(b : A) * d, by
    have h : (b : A) * d ∈ 𝒜 (i + j) := mul_mem_graded b.2 d.2
    simpa only [k] using h⟩
  refine ⟨k, num, den, fun x ↦ ?_, fun x ↦ ?_⟩
  · exact x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hb x) (hd x)
  · change f x * g x = _
    rw [hf x, hg x, Localization.mk_mul]
    congr 1

/-- The positive-fraction product is stable under local gluing. -/
theorem isLocallyPositiveSectionFraction_mul_locallyPositiveSectionFraction
    (m n : ℕ) {U : Opens X} {f g : ∀ x : U, PositiveFiber 𝒜 x.1}
    (hf : (isLocallyPositiveSectionFraction 𝒜 m).pred f)
    (hg : (isLocallyPositiveSectionFraction 𝒜 n).pred g) :
    (isLocallyPositiveSectionFraction 𝒜 (m + n)).pred (fun x ↦ f x * g x) := by
  intro x
  rcases hf x with ⟨V, hxV, iV, hV⟩
  rcases hg x with ⟨W, hxW, iW, hW⟩
  let Z := V ⊓ W
  let iZV : Z ⟶ V := Opens.infLELeft V W
  let iZW : Z ⟶ W := Opens.infLERight V W
  have hxZ : x.1 ∈ Z := ⟨hxV, hxW⟩
  refine ⟨Z, hxZ, iZV ≫ iV, ?_⟩
  exact isPositiveSectionFraction_mul_positiveSectionFraction 𝒜 m n
    ((isPositiveSectionFractionPrelocal 𝒜 m).res iZV _ hV)
    ((isPositiveSectionFractionPrelocal 𝒜 n).res iZW _ hW)

/-- The presheaf-level multiplication pairing of positive twists. -/
noncomputable def positivePositivePairingPresheaf (m n : ℕ) :
    PresheafOfModules.Monoidal.tensorObj (R := (Proj 𝒜).sheaf.obj)
      (positiveModulePresheaf 𝒜 m) (positiveModulePresheaf 𝒜 n) ⟶
      positiveModulePresheaf 𝒜 (m + n) where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun p q ↦ ⟨fun x ↦ p.1 x * q.1 x,
      isLocallyPositiveSectionFraction_mul_locallyPositiveSectionFraction
        𝒜 m n p.2 q.2⟩)
    (by
      intro p q r
      apply Subtype.ext
      funext x
      exact add_mul _ _ _)
    (by
      intro r p q
      apply Subtype.ext
      funext x
      change ((r.1 x).val * p.1 x) * q.1 x =
        (r.1 x).val * (p.1 x * q.1 x)
      ring)
    (by
      intro p q r
      apply Subtype.ext
      funext x
      exact mul_add _ _ _)
    (by
      intro r p q
      apply Subtype.ext
      funext x
      change p.1 x * ((r.1 x).val * q.1 x) =
        (r.1 x).val * (p.1 x * q.1 x)
      ring)
  naturality := by
    intro U V i
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro p q
    apply Subtype.ext
    funext x
    rfl

/-- The sheaf-level multiplication pairing `O(m) ⊗ O(n) → O(m+n)`. -/
noncomputable def positivePositivePairing (m n : ℕ) :
    schemeModuleTensor (positiveSheafOfModules 𝒜 m)
      (positiveSheafOfModules 𝒜 n) ⟶
      positiveSheafOfModules 𝒜 (m + n) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)).homEquiv _ _).symm
      (positivePositivePairingPresheaf 𝒜 m n)

end ProjectiveNegativeTwist
end PfaffianDescent
