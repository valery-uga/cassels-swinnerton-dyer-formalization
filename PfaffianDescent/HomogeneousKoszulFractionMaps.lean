import PfaffianDescent.HomogeneousFractionCommonDenominator

/-! SOURCE ONLY / UNVERIFIED. Genuine fraction-model maps of the actual
three-quadric negative-twist complex. No normalized regularity assumed. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open AlgebraicGeometry MvPolynomial
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K
variable (p : Ideal (MvPolynomial (Fin 4) K)) [p.IsPrime]
local notation "R0" => HomogeneousLocalization.AtPrime PS p

/-- Three actual stalk fraction modules. -/
abbrev homogeneousKoszulFractionTriple (m : ℕ) := (stalkSubmodule PS p m) × (stalkSubmodule PS p m) × (stalkSubmodule PS p m)

def homogeneousKoszulFractionFirst (f g h : PS 2) :
    (stalkSubmodule PS p 6) →ₗ[R0] homogeneousKoszulFractionTriple p 4 where
  toFun z := (mulHomogeneousStalk PS p h 4 z,
    -mulHomogeneousStalk PS p g 4 z, mulHomogeneousStalk PS p f 4 z)
  map_add' _ _ := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add, map_add]
    · apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add, neg_add]
  map_smul' _ _ := by
    apply Prod.ext
    · simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, map_smul]
    · apply Prod.ext <;> simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, map_smul, smul_neg]

def homogeneousKoszulFractionMiddle (f g h : PS 2) :
    homogeneousKoszulFractionTriple p 4 →ₗ[R0] homogeneousKoszulFractionTriple p 2 where
  toFun z := (-mulHomogeneousStalk PS p g 2 z.1 - mulHomogeneousStalk PS p h 2 z.2.1,
    mulHomogeneousStalk PS p f 2 z.1 - mulHomogeneousStalk PS p h 2 z.2.2,
    mulHomogeneousStalk PS p f 2 z.2.1 + mulHomogeneousStalk PS p g 2 z.2.2)
  map_add' _ _ := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
    · apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add] <;> abel
  map_smul' _ _ := by
    apply Prod.ext
    · simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, map_smul, smul_sub, smul_neg]
    · apply Prod.ext <;> simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, map_smul, smul_sub, smul_add]

def homogeneousKoszulFractionLast (f g h : PS 2) :
    homogeneousKoszulFractionTriple p 2 →ₗ[R0] (stalkSubmodule PS p 0) where
  toFun z := mulHomogeneousStalk PS p f 0 z.1 +
    mulHomogeneousStalk PS p g 0 z.2.1 + mulHomogeneousStalk PS p h 0 z.2.2
  map_add' _ _ := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
  map_smul' _ _ := by
    simp only [RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, map_smul, smul_add]

/-- The cycles are actual fraction cycles, not an input comparison square. -/
theorem homogeneousKoszulFraction_middle_first_zero (f g h : PS 2) :
    (homogeneousKoszulFractionMiddle p f g h).comp
      (homogeneousKoszulFractionFirst p f g h) = 0 := by
  apply LinearMap.ext
  intro z
  let ff := algebraMap (MvPolynomial (Fin 4) K) (Localization p.primeCompl) f.val
  let gg := algebraMap (MvPolynomial (Fin 4) K) (Localization p.primeCompl) g.val
  let hh := algebraMap (MvPolynomial (Fin 4) K) (Localization p.primeCompl) h.val
  apply Prod.ext
  · apply Subtype.ext
    change -(gg * (hh * z.val)) - hh * (-(gg * z.val)) = 0
    ring
  · apply Prod.ext <;> apply Subtype.ext
    · change ff * (hh * z.val) - hh * (ff * z.val) = 0
      ring
    · change ff * (-(gg * z.val)) + gg * (ff * z.val) = 0
      ring

theorem homogeneousKoszulFraction_last_middle_zero (f g h : PS 2) :
    (homogeneousKoszulFractionLast p f g h).comp
      (homogeneousKoszulFractionMiddle p f g h) = 0 := by
  apply LinearMap.ext
  intro z
  let ff := algebraMap (MvPolynomial (Fin 4) K) (Localization p.primeCompl) f.val
  let gg := algebraMap (MvPolynomial (Fin 4) K) (Localization p.primeCompl) g.val
  let hh := algebraMap (MvPolynomial (Fin 4) K) (Localization p.primeCompl) h.val
  apply Subtype.ext
  change ff * (-(gg * z.1.val) - hh * z.2.1.val) +
    gg * (ff * z.1.val - hh * z.2.2.val) +
    hh * (ff * z.2.1.val + gg * z.2.2.val) = 0
  ring

end PfaffianDescent.ProjectiveNegativeTwist
