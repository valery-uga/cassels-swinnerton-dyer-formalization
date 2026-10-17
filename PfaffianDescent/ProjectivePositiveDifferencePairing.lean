import PfaffianDescent.ProjectivePositiveTwist

/-!
# Positive difference of projective twists

A positive degree-`m` twist times a negative degree-`n` twist has positive
degree `m-n` when `n ≤ m`.
-/

noncomputable section

namespace PfaffianDescent

open scoped DirectSum Pointwise TensorProduct
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

universe u

namespace ProjectiveNegativeTwist

variable {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

section Stalk

variable (𝔭 : Ideal A) [𝔭.IsPrime]

local notation "Rₚ" => Localization 𝔭.primeCompl
local notation "Rₚ₀" => HomogeneousLocalization.AtPrime 𝒜 𝔭

/-- At a homogeneous prime, a positive degree-`m` fraction times a negative
degree-`n` fraction is positive of degree `m-n` when `n ≤ m`. -/
theorem positiveFraction_mul_fraction_mem_toPositive_of_le
    (m n : ℕ) (hnm : n ≤ m) {x y : Rₚ}
    (hx : IsPositiveFraction 𝒜 𝔭 m x)
    (hy : IsFraction 𝒜 𝔭 n y) :
    IsPositiveFraction 𝒜 𝔭 (m - n) (x * y) := by
  rcases hx with rfl | ⟨i, a, b, hb, rfl⟩
  · simpa only [zero_mul] using positiveFraction_zero_mem 𝒜 𝔭 (m - n)
  rcases hy with rfl | ⟨j, c, d, hd, rfl⟩
  · simpa only [mul_zero] using positiveFraction_zero_mem 𝒜 𝔭 (m - n)
  right
  let k := i + j + n
  let num : 𝒜 ((m - n) + k) := ⟨(a : A) * c, by
    have h : (a : A) * c ∈ 𝒜 ((m + i) + j) := mul_mem_graded a.2 c.2
    rw [show (m + i) + j = (m - n) + k by
      dsimp [k]
      omega] at h
    exact h⟩
  let den : 𝒜 k := ⟨(b : A) * d, by
    have h : (b : A) * d ∈ 𝒜 (i + (j + n)) := mul_mem_graded b.2 d.2
    simpa only [k, add_assoc] using h⟩
  refine ⟨k, num, den, 𝔭.primeCompl.mul_mem hb hd, ?_⟩
  simp only [num, den, Localization.mk_mul]
  congr 1

/-- The positive-result mixed product at a homogeneous prime, packaged as a
bilinear map of the concrete twist stalk models. -/
def positiveNegativePositiveDifferenceStalkBilinear
    (m n : ℕ) (hnm : n ≤ m) :
    positiveStalkSubmodule 𝒜 𝔭 m →ₗ[Rₚ₀]
      stalkSubmodule 𝒜 𝔭 n →ₗ[Rₚ₀] positiveStalkSubmodule 𝒜 𝔭 (m - n) where
  toFun p :=
    { toFun := fun q ↦ ⟨p.1 * q.1,
        positiveFraction_mul_fraction_mem_toPositive_of_le 𝒜 𝔭 m n hnm p.2 q.2⟩
      map_add' := by
        intro q r
        apply Subtype.ext
        exact mul_add _ _ _
      map_smul' := by
        intro r q
        apply Subtype.ext
        change p.1 * (r.val * q.1) = r.val * (p.1 * q.1)
        ring }
  map_add' := by
    intro p q
    ext r
    change (p.1 + q.1) * r.1 = p.1 * r.1 + q.1 * r.1
    ring
  map_smul' := by
    intro r p
    ext q
    change (r.val * p.1) * q.1 = r.val * (p.1 * q.1)
    ring

/-- On a degree-one chart, the positive-result mixed product sends the
standard generators in degrees `m` and `-n` to the standard generator in
degree `m-n`. -/
theorem positiveLocalGenerator_mul_localGenerator_toPositive_of_le
    (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl)
    (m n : ℕ) (hnm : n ≤ m) :
    ⟨(positiveLocalGenerator 𝒜 𝔭 f hf m) *
        (localGenerator 𝒜 𝔭 f hf n).1,
      positiveFraction_mul_fraction_mem_toPositive_of_le 𝒜 𝔭 m n hnm
        (positiveLocalGenerator 𝒜 𝔭 f hf m).2
        (localGenerator 𝒜 𝔭 f hf n).2⟩ =
      positiveLocalGenerator 𝒜 𝔭 f hf (m - n) := by
  apply Subtype.ext
  change algebraMap A Rₚ ((degreeOnePower 𝒜 f m : 𝒜 m) : A) *
      Localization.mk 1
        ⟨((degreeOnePower 𝒜 f n : 𝒜 n) : A),
          𝔭.primeCompl.pow_mem hf n⟩ =
      algebraMap A Rₚ ((degreeOnePower 𝒜 f (m - n) : 𝒜 (m - n)) : A)
  rw [← Localization.mk_one_eq_algebraMap]
  rw [← Localization.mk_one_eq_algebraMap]
  rw [Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, one_mul, mul_one, degreeOnePower]
  rw [← pow_add, add_comm n (m - n), Nat.sub_add_cancel hnm]

/-- Evaluation of the positive-result mixed stalk bilinear map on the
standard degree-one generators. -/
theorem positiveNegativePositiveDifferenceStalkBilinear_generators
    (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl)
    (m n : ℕ) (hnm : n ≤ m) :
    positiveNegativePositiveDifferenceStalkBilinear 𝒜 𝔭 m n hnm
      (positiveLocalGenerator 𝒜 𝔭 f hf m)
      (localGenerator 𝒜 𝔭 f hf n) =
      positiveLocalGenerator 𝒜 𝔭 f hf (m - n) :=
  positiveLocalGenerator_mul_localGenerator_toPositive_of_le
    𝒜 𝔭 f hf m n hnm

/-- The standard degree-one bases give a concrete linear equivalence from
the tensor of the positive and negative stalk twists to the positive
difference twist. -/
noncomputable def positiveNegativePositiveDifferenceStalkLinearEquiv
    (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl)
    (m n : ℕ) (_hnm : n ≤ m) :
    positiveStalkSubmodule 𝒜 𝔭 m ⊗[Rₚ₀]
      stalkSubmodule 𝒜 𝔭 n ≃ₗ[Rₚ₀]
      positiveStalkSubmodule 𝒜 𝔭 (m - n) :=
  TensorProduct.congr
    (positiveLocalTrivialization 𝒜 𝔭 f hf m).symm
    (localTrivialization 𝒜 𝔭 f hf n).symm ≪≫ₗ
  TensorProduct.lid Rₚ₀ Rₚ₀ ≪≫ₗ
  positiveLocalTrivialization 𝒜 𝔭 f hf (m - n)

/-- The positive-difference local tensor equivalence sends the standard
generators to the standard target generator. -/
theorem positiveNegativePositiveDifferenceStalkLinearEquiv_generators
    (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl)
    (m n : ℕ) (hnm : n ≤ m) :
    positiveNegativePositiveDifferenceStalkLinearEquiv 𝒜 𝔭 f hf m n hnm
      ((positiveLocalGenerator 𝒜 𝔭 f hf m) ⊗ₜ[Rₚ₀]
        (localGenerator 𝒜 𝔭 f hf n)) =
      positiveLocalGenerator 𝒜 𝔭 f hf (m - n) := by
  have hpos : (positiveLocalTrivialization 𝒜 𝔭 f hf m).symm
      (positiveLocalGenerator 𝒜 𝔭 f hf m) = 1 := by
    apply (positiveLocalTrivialization 𝒜 𝔭 f hf m).injective
    rw [LinearEquiv.apply_symm_apply]
    simp [positiveLocalTrivialization, positiveLocalGeneratorLinearMap,
      LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply]
  have hneg : (localTrivialization 𝒜 𝔭 f hf n).symm
      (localGenerator 𝒜 𝔭 f hf n) = 1 := by
    apply (localTrivialization 𝒜 𝔭 f hf n).injective
    rw [LinearEquiv.apply_symm_apply]
    simp [localTrivialization, localGeneratorLinearMap,
      LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply]
  simp only [positiveNegativePositiveDifferenceStalkLinearEquiv,
    LinearEquiv.trans_apply, TensorProduct.congr_tmul, TensorProduct.lid_tmul,
    hpos, hneg]
  simp [positiveLocalTrivialization, positiveLocalGeneratorLinearMap,
    LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply]

end Stalk

local notation "X" => ProjectiveSpectrum.top 𝒜

/-- A positive degree-`m` fixed fraction times a negative degree-`n` fixed
fraction is positive of degree `m-n` when `n ≤ m`. -/
theorem isPositiveSectionFraction_mul_sectionFraction_toPositive_of_le
    (m n : ℕ) (hnm : n ≤ m) {U : Opens X}
    {f g : ∀ x : U, PositiveFiber 𝒜 x.1}
    (hf : IsPositiveSectionFraction 𝒜 m f)
    (hg : IsSectionFraction 𝒜 n g) :
    IsPositiveSectionFraction 𝒜 (m - n) (fun x ↦ f x * g x) := by
  rcases hf with rfl | ⟨i, a, b, hb, hf⟩
  · exact Or.inl (funext fun x ↦ zero_mul (g x))
  rcases hg with rfl | ⟨j, c, d, hd, hg⟩
  · exact Or.inl (funext fun x ↦ mul_zero (f x))
  right
  let k := i + j + n
  let num : 𝒜 ((m - n) + k) := ⟨(a : A) * c, by
    have h : (a : A) * c ∈ 𝒜 ((m + i) + j) := mul_mem_graded a.2 c.2
    rw [show (m + i) + j = (m - n) + k by
      dsimp [k]
      omega] at h
    exact h⟩
  let den : 𝒜 k := ⟨(b : A) * d, by
    have h : (b : A) * d ∈ 𝒜 (i + (j + n)) := mul_mem_graded b.2 d.2
    simpa only [k, add_assoc] using h⟩
  refine ⟨k, num, den, fun x ↦ ?_, fun x ↦ ?_⟩
  · exact x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hb x) (hd x)
  · change f x * g x = _
    rw [hf x, hg x, Localization.mk_mul]
    congr 1

/-- The positive-difference product is stable under local gluing. -/
theorem isLocallyPositiveSectionFraction_mul_locallySectionFraction_toPositive_of_le
    (m n : ℕ) (hnm : n ≤ m) {U : Opens X}
    {f g : ∀ x : U, PositiveFiber 𝒜 x.1}
    (hf : (isLocallyPositiveSectionFraction 𝒜 m).pred f)
    (hg : (isLocallySectionFraction 𝒜 n).pred g) :
    (isLocallyPositiveSectionFraction 𝒜 (m - n)).pred (fun x ↦ f x * g x) := by
  intro x
  rcases hf x with ⟨V, hxV, iV, hV⟩
  rcases hg x with ⟨W, hxW, iW, hW⟩
  let Z := V ⊓ W
  let iZV : Z ⟶ V := Opens.infLELeft V W
  let iZW : Z ⟶ W := Opens.infLERight V W
  have hxZ : x.1 ∈ Z := ⟨hxV, hxW⟩
  refine ⟨Z, hxZ, iZV ≫ iV, ?_⟩
  exact isPositiveSectionFraction_mul_sectionFraction_toPositive_of_le 𝒜 m n hnm
    ((isPositiveSectionFractionPrelocal 𝒜 m).res iZV _ hV)
    ((isSectionFractionPrelocal 𝒜 n).res iZW _ hW)

/-- The presheaf-level positive-difference pairing
`O(m) ⊗ O(-n) → O(m-n)` for `n ≤ m`. -/
noncomputable def positiveNegativePositiveDifferencePairingPresheaf
    (m n : ℕ) (hnm : n ≤ m) :
    PresheafOfModules.Monoidal.tensorObj (R := (Proj 𝒜).sheaf.obj)
      (positiveModulePresheaf 𝒜 m) (modulePresheaf 𝒜 n) ⟶
      positiveModulePresheaf 𝒜 (m - n) where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun p q ↦ ⟨fun x ↦ p.1 x * q.1 x,
      isLocallyPositiveSectionFraction_mul_locallySectionFraction_toPositive_of_le
        𝒜 m n hnm p.2 q.2⟩)
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

/-- The sheaf-level positive-difference pairing
`O(m) ⊗ O(-n) → O(m-n)` for `n ≤ m`. -/
noncomputable def positiveNegativePositiveDifferencePairing
    (m n : ℕ) (hnm : n ≤ m) :
    schemeModuleTensor (positiveSheafOfModules 𝒜 m) (sheafOfModules 𝒜 n) ⟶
      positiveSheafOfModules 𝒜 (m - n) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)).homEquiv _ _).symm
      (positiveNegativePositiveDifferencePairingPresheaf 𝒜 m n hnm)

/-- At equal degrees, the positive-result pairing becomes the usual
positive-negative pairing after converting the zero positive twist to the
ordinary zero twist. -/
theorem positiveNegativePositiveDifferencePairing_five_five_factorization :
    positiveNegativePositiveDifferencePairing 𝒜 5 5 (by omega) ≫
      positiveZeroToZeroTwist 𝒜 =
    positiveNegativePairing 𝒜 5 := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_right]
  have hdiff : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 5).val
        (sheafOfModules 𝒜 5).val) (positiveSheafOfModules 𝒜 0)
      (positiveNegativePositiveDifferencePairing 𝒜 5 5 (by omega)) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 5 5 (by omega) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  rw [hdiff]
  have hpair : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 5).val
        (sheafOfModules 𝒜 5).val) (sheafOfModules 𝒜 0)
      (positiveNegativePairing 𝒜 5) =
      positiveNegativePairingPresheaf 𝒜 5 := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  rw [hpair]
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  rfl

/-- Multiplication by a degree-one form on the negative factor changes the
`(5,5)` positive-result pairing into the `(5,4)` pairing. -/
theorem positiveNegativePositiveDifferencePairingPresheaf_five_four_mul_naturality
    (s : 𝒜 1) :
    PresheafOfModules.Monoidal.tensorHom
      (𝟙 (positiveModulePresheaf 𝒜 5)) (mulHomogeneous 𝒜 s 4).val ≫
        positiveNegativePositiveDifferencePairingPresheaf 𝒜 5 4 (by omega) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 5 5 (by omega) ≫
        (positiveMulHomogeneous 𝒜 s 0).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  change p.1 x * (algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * q.1 x) =
    algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * (p.1 x * q.1 x)
  ring

/-- Sheafified form of
`positiveNegativePositiveDifferencePairingPresheaf_five_four_mul_naturality`. -/
theorem positiveNegativePositiveDifferencePairing_five_four_mul_naturality
    (s : 𝒜 1) :
    schemeModuleTensorMap (𝟙 (positiveSheafOfModules 𝒜 5))
      (mulHomogeneous 𝒜 s 4) ≫
        positiveNegativePositiveDifferencePairing 𝒜 5 4 (by omega) =
      positiveNegativePositiveDifferencePairing 𝒜 5 5 (by omega) ≫
        positiveMulHomogeneous 𝒜 s 0 := by
  rw [schemeModuleTensorMap_eq_sheafification]
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  have hfour : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 5).val
        (sheafOfModules 𝒜 4).val) (positiveSheafOfModules 𝒜 1)
      (positiveNegativePositiveDifferencePairing 𝒜 5 4 (by omega)) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 5 4 (by omega) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  have hfive : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 5).val
        (sheafOfModules 𝒜 5).val) (positiveSheafOfModules 𝒜 0)
      (positiveNegativePositiveDifferencePairing 𝒜 5 5 (by omega)) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 5 5 (by omega) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [hfour]
  erw [adj.homEquiv_naturality_right]
  rw [hfive]
  exact positiveNegativePositiveDifferencePairingPresheaf_five_four_mul_naturality 𝒜 s

/-- Multiplication by a degree-one form on the negative factor changes the
`(5,4)` positive-result pairing into the `(5,3)` pairing. -/
theorem positiveNegativePositiveDifferencePairingPresheaf_five_three_mul_naturality
    (s : 𝒜 1) :
    PresheafOfModules.Monoidal.tensorHom
      (𝟙 (positiveModulePresheaf 𝒜 5)) (mulHomogeneous 𝒜 s 3).val ≫
        positiveNegativePositiveDifferencePairingPresheaf 𝒜 5 3 (by omega) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 5 4 (by omega) ≫
        (positiveMulHomogeneous 𝒜 s 1).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  change p.1 x * (algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * q.1 x) =
    algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * (p.1 x * q.1 x)
  ring

/-- Sheafified form of
`positiveNegativePositiveDifferencePairingPresheaf_five_three_mul_naturality`. -/
theorem positiveNegativePositiveDifferencePairing_five_three_mul_naturality
    (s : 𝒜 1) :
    schemeModuleTensorMap (𝟙 (positiveSheafOfModules 𝒜 5))
      (mulHomogeneous 𝒜 s 3) ≫
        positiveNegativePositiveDifferencePairing 𝒜 5 3 (by omega) =
      positiveNegativePositiveDifferencePairing 𝒜 5 4 (by omega) ≫
        positiveMulHomogeneous 𝒜 s 1 := by
  rw [schemeModuleTensorMap_eq_sheafification]
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  have hthree : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 5).val
        (sheafOfModules 𝒜 3).val) (positiveSheafOfModules 𝒜 2)
      (positiveNegativePositiveDifferencePairing 𝒜 5 3 (by omega)) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 5 3 (by omega) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  have hfour : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 5).val
        (sheafOfModules 𝒜 4).val) (positiveSheafOfModules 𝒜 1)
      (positiveNegativePositiveDifferencePairing 𝒜 5 4 (by omega)) =
      positiveNegativePositiveDifferencePairingPresheaf 𝒜 5 4 (by omega) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [hthree]
  erw [adj.homEquiv_naturality_right]
  rw [hfour]
  exact positiveNegativePositiveDifferencePairingPresheaf_five_three_mul_naturality 𝒜 s

end ProjectiveNegativeTwist
end PfaffianDescent
