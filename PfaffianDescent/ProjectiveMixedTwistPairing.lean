import PfaffianDescent.ProjectivePositiveTwist

/-!
# Mixed positive--negative projective twist pairings

This supplies the degree-subtraction pairing between a positive projective
twist and a negative one.  It is the missing algebraic interface for twisting
the cubic hypersurface restriction sequence by a positive line bundle.
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

/-- At a homogeneous prime, the mixed product has the expected difference
degree before passing to sheaves. -/
theorem positiveFraction_mul_fraction_mem_of_le
    (m n : ℕ) (hmn : m ≤ n) {x y : Rₚ}
    (hx : IsPositiveFraction 𝒜 𝔭 m x)
    (hy : IsFraction 𝒜 𝔭 n y) :
    IsFraction 𝒜 𝔭 (n - m) (x * y) := by
  rcases hx with rfl | ⟨i, a, b, hb, rfl⟩
  · simpa only [zero_mul] using zero_mem 𝒜 𝔭 (n - m)
  rcases hy with rfl | ⟨j, c, d, hd, rfl⟩
  · simpa only [mul_zero] using zero_mem 𝒜 𝔭 (n - m)
  right
  let k := m + i + j
  let num : 𝒜 k := ⟨(a : A) * c, by
    have h : (a : A) * c ∈ 𝒜 ((m + i) + j) := mul_mem_graded a.2 c.2
    simpa only [k, add_assoc] using h⟩
  let den : 𝒜 (k + (n - m)) := ⟨(b : A) * d, by
    have h : (b : A) * d ∈ 𝒜 (i + (j + n)) := mul_mem_graded b.2 d.2
    rw [show i + (j + n) = k + (n - m) by
      dsimp [k]
      omega] at h
    exact h⟩
  refine ⟨k, num, den, 𝔭.primeCompl.mul_mem hb hd, ?_⟩
  simp only [num, den, Localization.mk_mul]
  congr 1

/-- In the standard local bases, the mixed product sends the positive
generator of degree `m` and the negative generator of degree `n` to the
negative generator of degree `n-m`. -/
theorem positiveLocalGenerator_mul_localGenerator_of_le
    (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl)
    (m n : ℕ) (hmn : m ≤ n) :
    ⟨(positiveLocalGenerator 𝒜 𝔭 f hf m) *
        (localGenerator 𝒜 𝔭 f hf n).1,
      positiveFraction_mul_fraction_mem_of_le 𝒜 𝔭 m n hmn
        (positiveLocalGenerator 𝒜 𝔭 f hf m).2
        (localGenerator 𝒜 𝔭 f hf n).2⟩ =
      localGenerator 𝒜 𝔭 f hf (n - m) := by
  apply Subtype.ext
  change algebraMap A Rₚ ((degreeOnePower 𝒜 f m : 𝒜 m) : A) *
      Localization.mk 1
        ⟨((degreeOnePower 𝒜 f n : 𝒜 n) : A),
          𝔭.primeCompl.pow_mem hf n⟩ =
      Localization.mk 1
        ⟨((degreeOnePower 𝒜 f (n - m) : 𝒜 (n - m)) : A),
          𝔭.primeCompl.pow_mem hf (n - m)⟩
  rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, one_mul, mul_one,
    degreeOnePower]
  rw [← pow_add, Nat.sub_add_cancel hmn]

/-- The stalkwise mixed product as an `Rₚ₀`-bilinear map.  Its value is the
ordinary product in the ambient localization, with the difference-degree
membership supplied by `positiveFraction_mul_fraction_mem_of_le`. -/
def positiveNegativeDifferenceStalkBilinear
    (m n : ℕ) (hmn : m ≤ n) :
    positiveStalkSubmodule 𝒜 𝔭 m →ₗ[Rₚ₀]
      stalkSubmodule 𝒜 𝔭 n →ₗ[Rₚ₀] stalkSubmodule 𝒜 𝔭 (n - m) where
  toFun p :=
    { toFun := fun q ↦ ⟨p.1 * q.1,
        positiveFraction_mul_fraction_mem_of_le 𝒜 𝔭 m n hmn p.2 q.2⟩
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

/-- The stalkwise bilinear map has the expected value on the standard local
generators. -/
theorem positiveNegativeDifferenceStalkBilinear_generators
    (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl)
    (m n : ℕ) (hmn : m ≤ n) :
    positiveNegativeDifferenceStalkBilinear 𝒜 𝔭 m n hmn
      (positiveLocalGenerator 𝒜 𝔭 f hf m)
      (localGenerator 𝒜 𝔭 f hf n) =
      localGenerator 𝒜 𝔭 f hf (n - m) :=
  positiveLocalGenerator_mul_localGenerator_of_le 𝒜 𝔭 f hf m n hmn

/-- The standard local bases give a concrete linear equivalence from the
tensor product of the mixed twist stalks to the difference twist stalk. -/
noncomputable def positiveNegativeDifferenceStalkLinearEquiv
    (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl)
    (m n : ℕ) (_hmn : m ≤ n) :
    positiveStalkSubmodule 𝒜 𝔭 m ⊗[Rₚ₀]
      stalkSubmodule 𝒜 𝔭 n ≃ₗ[Rₚ₀]
      stalkSubmodule 𝒜 𝔭 (n - m) :=
  TensorProduct.congr
    (positiveLocalTrivialization 𝒜 𝔭 f hf m).symm
    (localTrivialization 𝒜 𝔭 f hf n).symm ≪≫ₗ
  TensorProduct.lid Rₚ₀ Rₚ₀ ≪≫ₗ
  localTrivialization 𝒜 𝔭 f hf (n - m)

/-- The local tensor equivalence sends the two standard generators to the
standard generator in the difference twist. -/
theorem positiveNegativeDifferenceStalkLinearEquiv_generators
    (f : 𝒜 1) (hf : (f : A) ∈ 𝔭.primeCompl)
    (m n : ℕ) (hmn : m ≤ n) :
    positiveNegativeDifferenceStalkLinearEquiv 𝒜 𝔭 f hf m n hmn
      ((positiveLocalGenerator 𝒜 𝔭 f hf m) ⊗ₜ[Rₚ₀]
        (localGenerator 𝒜 𝔭 f hf n)) =
      localGenerator 𝒜 𝔭 f hf (n - m) := by
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
  simp only [positiveNegativeDifferenceStalkLinearEquiv,
    LinearEquiv.trans_apply, TensorProduct.congr_tmul, TensorProduct.lid_tmul,
    hpos, hneg]
  simp [localTrivialization, localGeneratorLinearMap,
    LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply]

end Stalk

local notation "X" => ProjectiveSpectrum.top 𝒜

/-- A positive degree-`m` fixed fraction times a negative degree-`n` fixed
fraction is a negative degree-`(n-m)` fixed fraction when `m ≤ n`. -/
theorem isPositiveSectionFraction_mul_sectionFraction_of_le
    (m n : ℕ) (hmn : m ≤ n) {U : Opens X}
    {f g : ∀ x : U, PositiveFiber 𝒜 x.1}
    (hf : IsPositiveSectionFraction 𝒜 m f)
    (hg : IsSectionFraction 𝒜 n g) :
    IsSectionFraction 𝒜 (n - m) (fun x ↦ f x * g x) := by
  rcases hf with rfl | ⟨i, a, b, hb, hf⟩
  · exact Or.inl (funext fun x ↦ zero_mul (g x))
  rcases hg with rfl | ⟨j, c, d, hd, hg⟩
  · exact Or.inl (funext fun x ↦ mul_zero (f x))
  right
  let k := m + i + j
  let num : 𝒜 k := ⟨(a : A) * c, by
    have h : (a : A) * c ∈ 𝒜 ((m + i) + j) := mul_mem_graded a.2 c.2
    simpa only [k, add_assoc] using h⟩
  let den : 𝒜 (k + (n - m)) := ⟨(b : A) * d, by
    have h : (b : A) * d ∈ 𝒜 (i + (j + n)) := mul_mem_graded b.2 d.2
    rw [show i + (j + n) = k + (n - m) by
      dsimp [k]
      omega] at h
    exact h⟩
  refine ⟨k, num, den, fun x ↦ ?_, fun x ↦ ?_⟩
  · exact x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hb x) (hd x)
  · change f x * g x = _
    rw [hf x, hg x, Localization.mk_mul]
    congr 1

/-- The mixed fixed-fraction product is stable under local gluing. -/
theorem isLocallyPositiveSectionFraction_mul_locallySectionFraction_of_le
    (m n : ℕ) (hmn : m ≤ n) {U : Opens X}
    {f g : ∀ x : U, PositiveFiber 𝒜 x.1}
    (hf : (isLocallyPositiveSectionFraction 𝒜 m).pred f)
    (hg : (isLocallySectionFraction 𝒜 n).pred g) :
    (isLocallySectionFraction 𝒜 (n - m)).pred (fun x ↦ f x * g x) := by
  intro x
  rcases hf x with ⟨V, hxV, iV, hV⟩
  rcases hg x with ⟨W, hxW, iW, hW⟩
  let Z := V ⊓ W
  let iZV : Z ⟶ V := Opens.infLELeft V W
  let iZW : Z ⟶ W := Opens.infLERight V W
  have hxZ : x.1 ∈ Z := ⟨hxV, hxW⟩
  refine ⟨Z, hxZ, iZV ≫ iV, ?_⟩
  exact isPositiveSectionFraction_mul_sectionFraction_of_le 𝒜 m n hmn
    ((isPositiveSectionFractionPrelocal 𝒜 m).res iZV _ hV)
    ((isSectionFractionPrelocal 𝒜 n).res iZW _ hW)

/-- The presheaf-level degree-subtraction pairing
`O(m) ⊗ O(-n) → O(-(n-m))`. -/
noncomputable def positiveNegativeDifferencePairingPresheaf
    (m n : ℕ) (hmn : m ≤ n) :
    PresheafOfModules.Monoidal.tensorObj (R := (Proj 𝒜).sheaf.obj)
      (positiveModulePresheaf 𝒜 m) (modulePresheaf 𝒜 n) ⟶
      modulePresheaf 𝒜 (n - m) where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun p q ↦
      ⟨fun x ↦ p.1 x * q.1 x,
        isLocallyPositiveSectionFraction_mul_locallySectionFraction_of_le
          𝒜 m n hmn p.2 q.2⟩)
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

/-- The sheaf-level degree-subtraction pairing
`O(m) ⊗ O(-n) → O(-(n-m))`. -/
noncomputable def positiveNegativeDifferencePairing
    (m n : ℕ) (hmn : m ≤ n) :
    schemeModuleTensor (positiveSheafOfModules 𝒜 m) (sheafOfModules 𝒜 n) ⟶
      sheafOfModules 𝒜 (n - m) :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)).homEquiv _ _).symm
      (positiveNegativeDifferencePairingPresheaf 𝒜 m n hmn)

/-- On the degree-one chart used for the cubic surface, multiplication by
the chart coordinate turns the mixed `(2,3)` pairing into the equal-degree
`(3,3)` pairing.  This is the presheaf calculation behind the local
isomorphism of the mixed pairing. -/
theorem positiveNegativeDifferencePairingPresheaf_two_three_mul_naturality
    (s : 𝒜 1) :
    PresheafOfModules.Monoidal.tensorHom (positiveMulHomogeneous 𝒜 s 2).val
      (𝟙 (modulePresheaf 𝒜 3)) ≫
        positiveNegativePairingPresheaf 𝒜 3 =
      positiveNegativeDifferencePairingPresheaf 𝒜 2 3 (by omega) ≫
        (mulHomogeneous 𝒜 s 0).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  change (algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * p.1 x) * q.1 x =
    algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * (p.1 x * q.1 x)
  ring

/-- Sheafified form of
`positiveNegativeDifferencePairingPresheaf_two_three_mul_naturality`. -/
theorem positiveNegativeDifferencePairing_two_three_mul_naturality
    (s : 𝒜 1) :
    schemeModuleTensorMap (positiveMulHomogeneous 𝒜 s 2)
      (𝟙 (sheafOfModules 𝒜 3)) ≫ positiveNegativePairing 𝒜 3 =
      positiveNegativeDifferencePairing 𝒜 2 3 (by omega) ≫
        mulHomogeneous 𝒜 s 0 := by
  rw [schemeModuleTensorMap_eq_sheafification]
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  have hpair :
      adj.homEquiv
        (PresheafOfModules.Monoidal.tensorObj
          (positiveSheafOfModules 𝒜 3).val (sheafOfModules 𝒜 3).val)
        (sheafOfModules 𝒜 0) (positiveNegativePairing 𝒜 3) =
      positiveNegativePairingPresheaf 𝒜 3 := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  have hdiff :
      adj.homEquiv
        (PresheafOfModules.Monoidal.tensorObj
          (positiveSheafOfModules 𝒜 2).val (sheafOfModules 𝒜 3).val)
        (sheafOfModules 𝒜 1)
        (positiveNegativeDifferencePairing 𝒜 2 3 (by omega)) =
      positiveNegativeDifferencePairingPresheaf 𝒜 2 3 (by omega) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [hpair]
  erw [adj.homEquiv_naturality_right]
  rw [hdiff]
  exact positiveNegativeDifferencePairingPresheaf_two_three_mul_naturality 𝒜 s

/-- The analogous coordinate-multiplication identity for the `(5,6)` mixed
pairing, which is the left term in the cubic restriction sequence after a
positive degree-five twist. -/
theorem positiveNegativeDifferencePairingPresheaf_five_six_mul_naturality
    (s : 𝒜 1) :
    PresheafOfModules.Monoidal.tensorHom (positiveMulHomogeneous 𝒜 s 5).val
      (𝟙 (modulePresheaf 𝒜 6)) ≫
        positiveNegativePairingPresheaf 𝒜 6 =
      positiveNegativeDifferencePairingPresheaf 𝒜 5 6 (by omega) ≫
        (mulHomogeneous 𝒜 s 0).val := by
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  change (algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * p.1 x) * q.1 x =
    algebraMap A (PositiveFiber 𝒜 x.1) (s : A) * (p.1 x * q.1 x)
  ring

/-- Sheafified form of
`positiveNegativeDifferencePairingPresheaf_five_six_mul_naturality`. -/
theorem positiveNegativeDifferencePairing_five_six_mul_naturality
    (s : 𝒜 1) :
    schemeModuleTensorMap (positiveMulHomogeneous 𝒜 s 5)
      (𝟙 (sheafOfModules 𝒜 6)) ≫ positiveNegativePairing 𝒜 6 =
      positiveNegativeDifferencePairing 𝒜 5 6 (by omega) ≫
        mulHomogeneous 𝒜 s 0 := by
  rw [schemeModuleTensorMap_eq_sheafification]
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  have hpair :
      adj.homEquiv
        (PresheafOfModules.Monoidal.tensorObj
          (positiveSheafOfModules 𝒜 6).val (sheafOfModules 𝒜 6).val)
        (sheafOfModules 𝒜 0) (positiveNegativePairing 𝒜 6) =
      positiveNegativePairingPresheaf 𝒜 6 := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  have hdiff :
      adj.homEquiv
        (PresheafOfModules.Monoidal.tensorObj
          (positiveSheafOfModules 𝒜 5).val (sheafOfModules 𝒜 6).val)
        (sheafOfModules 𝒜 1)
        (positiveNegativeDifferencePairing 𝒜 5 6 (by omega)) =
      positiveNegativeDifferencePairingPresheaf 𝒜 5 6 (by omega) := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  erw [adj.homEquiv_naturality_left]
  rw [hpair]
  erw [adj.homEquiv_naturality_right]
  rw [hdiff]
  exact positiveNegativeDifferencePairingPresheaf_five_six_mul_naturality 𝒜 s

end ProjectiveNegativeTwist
end PfaffianDescent
