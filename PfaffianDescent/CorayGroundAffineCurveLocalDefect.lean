import PfaffianDescent.CorayGroundAffineJetSurjectivity
import PfaffianDescent.CorayCurveNormalizationFiniteLength

/-!
# The original ground curve stalk has positive finite normalization defect

The source is the literal two-equation quotient of ORIGINAL K-polynomials.
Its actual full jet is surjective by separable minimal-polynomial preimages.
The actual point ideal pulls back to the ORIGINAL residue evaluation kernel.
The actual K-curve localization has cotangent rank at least two and, on the
primitive integral branch, positive finite normalization-defect length.

No jet, cotangent, normalization-finiteness or finite-length certificate is
supplied. Global genus and the reducible branches remain open.
STATUS: UNVERIFIED source only. Root owns compiler checks.
-/

noncomputable section
namespace PfaffianDescent.Coray

open MvPolynomial TrivSqZeroExt IsLocalRing Module

universe u
variable {K M : Type u} [Field K] [Field M] [Algebra K M]

/-- The actual original ground curve quotient carries its actual residue jet. -/
def groundAffineCurvePointJet
    (p q : MvPolynomial (Fin 3) K) (x : Fin 3 → M) (pivot : Fin 3)
    (hp : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv pivot p).eval₂ (algebraMap K M) x ≠ 0)
    (hq : groundAffineSurfaceJetMap p x pivot q = 0) :
    affineCurveRing p q →ₐ[K] CubicSurfaceFirstJet M := by
  refine Ideal.Quotient.liftₐ (affineCurveIdeal p q)
    (groundAffineSurfaceJetMap p x pivot) ?_
  intro r hr
  have hle : affineCurveIdeal p q ≤
      RingHom.ker (groundAffineSurfaceJetMap p x pivot).toRingHom := by
    apply Ideal.span_le.mpr
    intro s hs
    rcases Set.mem_insert_iff.mp hs with hsp | hsq
    · rw [hsp]
      exact groundAffineSurfaceJetMap_equation_zero p x pivot hp hpivot
    · rw [Set.mem_singleton_iff.mp hsq]
      exact hq
  exact hle hr

/-- Actual original curve classes evaluate by the actual original jet map. -/
theorem groundAffineCurvePointJet_apply_mk
    (p q f : MvPolynomial (Fin 3) K) (x : Fin 3 → M) (pivot : Fin 3)
    (hp : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv pivot p).eval₂ (algebraMap K M) x ≠ 0)
    (hq : groundAffineSurfaceJetMap p x pivot q = 0) :
    groundAffineCurvePointJet p q x pivot hp hpivot hq
        (Ideal.Quotient.mk (affineCurveIdeal p q) f) =
      groundAffineSurfaceJetMap p x pivot f := rfl

/-- This is the actual ORIGINAL ground residue point, identified by pullback
of its actual point ideal to the actual ground polynomial evaluation kernel. -/
theorem groundAffineCurve_actualPointIdeal_comap_mk
    (p q : MvPolynomial (Fin 3) K) (x : Fin 3 → M) (pivot : Fin 3)
    (hp : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv pivot p).eval₂ (algebraMap K M) x ≠ 0)
    (hq : groundAffineSurfaceJetMap p x pivot q = 0) :
    (RingHom.ker (fullJetResidueMap
      (groundAffineCurvePointJet p q x pivot hp hpivot hq).toRingHom)).comap
        (Ideal.Quotient.mk (affineCurveIdeal p q)) =
      RingHom.ker (MvPolynomial.eval₂Hom (algebraMap K M) x) := by
  ext f
  change (groundAffineCurvePointJet p q x pivot hp hpivot hq
    (Ideal.Quotient.mk (affineCurveIdeal p q) f)).fst = 0 ↔
      f.eval₂ (algebraMap K M) x = 0
  rw [groundAffineCurvePointJet_apply_mk, groundAffineSurfaceJetMap_fst]

/-- Surjectivity is constructed with ORIGINAL ground polynomial preimages. -/
theorem groundAffineCurvePointJet_surjective
    [CharZero K] [FiniteDimensional K M]
    (p q : MvPolynomial (Fin 3) K) (x : Fin 3 → M) (pivot : Fin 3)
    (hp : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv pivot p).eval₂ (algebraMap K M) x ≠ 0)
    (hq : groundAffineSurfaceJetMap p x pivot q = 0)
    (heval : Function.Surjective (MvPolynomial.eval₂Hom (algebraMap K M) x)) :
    Function.Surjective (groundAffineCurvePointJet p q x pivot hp hpivot hq) := by
  intro z
  obtain ⟨f, hf⟩ := groundAffineSurfaceJetMap_surjective p x pivot heval z
  exact ⟨Ideal.Quotient.mk (affineCurveIdeal p q) f,
    (groundAffineCurvePointJet_apply_mk p q f x pivot hp hpivot hq).trans hf⟩

/-- Actual cotangent rank at the actual ORIGINAL ground curve stalk, over
that stalk's OWN residue field. No supplied rank or jet premise. -/
theorem groundAffineCurve_actualPoint_cotangent_finrank_ge_two
    [CharZero K] [FiniteDimensional K M]
    (p q : MvPolynomial (Fin 3) K) (x : Fin 3 → M) (pivot : Fin 3)
    (hp : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv pivot p).eval₂ (algebraMap K M) x ≠ 0)
    (hq : groundAffineSurfaceJetMap p x pivot q = 0)
    (heval : Function.Surjective (MvPolynomial.eval₂Hom (algebraMap K M) x)) :
    let phi := (groundAffineCurvePointJet p q x pivot hp hpivot hq).toRingHom
    let hphi : Function.Surjective phi :=
      groundAffineCurvePointJet_surjective p q x pivot hp hpivot hq heval
    let P := RingHom.ker (fullJetResidueMap phi)
    letI : P.IsPrime := (fullJetResidueIdeal_isMaximal phi hphi).isPrime
    2 ≤ finrank (ResidueField (Localization.AtPrime P))
      (CotangentSpace (Localization.AtPrime P)) := by
  exact fullJetAtActualPoint_cotangent_finrank_ge_two _
    (groundAffineCurvePointJet_surjective p q x pivot hp hpivot hq heval)

/-- On the primitive integral branch, the actual ORIGINAL ground stalk has
an actual nonzero normalization quotient, constructed from its actual jet. -/
theorem groundAffineCurve_actualPoint_normalizationDefect_nontrivial
    [CharZero K] [FiniteDimensional K M]
    (p q : MvPolynomial (Fin 3) K) (hpirr : Irreducible p)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 3) K)))
    [hcurve : (affineCurveIdeal p q).IsPrime]
    (x : Fin 3 → M) (pivot : Fin 3)
    (hp : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv pivot p).eval₂ (algebraMap K M) x ≠ 0)
    (hq : groundAffineSurfaceJetMap p x pivot q = 0)
    (heval : Function.Surjective (MvPolynomial.eval₂Hom (algebraMap K M) x)) :
    let phi := (groundAffineCurvePointJet p q x pivot hp hpivot hq).toRingHom
    let hphi : Function.Surjective phi :=
      groundAffineCurvePointJet_surjective p q x pivot hp hpivot hq heval
    let P := RingHom.ker (fullJetResidueMap phi)
    letI : P.IsPrime := (fullJetResidueIdeal_isMaximal phi hphi).isPrime
    Nontrivial (localNormalizationDefect (Localization.AtPrime P)
      (FractionRing (Localization.AtPrime P))) := by
  let phi := (groundAffineCurvePointJet p q x pivot hp hpivot hq).toRingHom
  let hphi : Function.Surjective phi :=
    groundAffineCurvePointJet_surjective p q x pivot hp hpivot hq heval
  let P := RingHom.ker (fullJetResidueMap phi)
  letI : P.IsPrime := (fullJetResidueIdeal_isMaximal phi hphi).isPrime
  letI : Ring.DimensionLEOne (Localization.AtPrime P) :=
    affineCurve_local_dimensionLEOne_of_prime p q hpirr hnot P
  exact localNormalizationDefect_nontrivial_of_surjective_fullJet
    (FractionRing (Localization.AtPrime P))
    (fullJetAtActualPoint phi hphi) (fullJetAtActualPoint_surjective phi hphi)

/-- The actual ORIGINAL ground stalk's normalization defect has positive
finite COMPOSITION length. Finite normalization is proved internally from
its actual finite-type characteristic-zero original ground equations. -/
theorem groundAffineCurve_actualPoint_normalizationDefect_length_pos_and_ne_top
    [CharZero K] [FiniteDimensional K M]
    (p q : MvPolynomial (Fin 3) K) (hpirr : Irreducible p)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 3) K)))
    [hcurve : (affineCurveIdeal p q).IsPrime]
    (x : Fin 3 → M) (pivot : Fin 3)
    (hp : p.eval₂ (algebraMap K M) x = 0)
    (hpivot : (pderiv pivot p).eval₂ (algebraMap K M) x ≠ 0)
    (hq : groundAffineSurfaceJetMap p x pivot q = 0)
    (heval : Function.Surjective (MvPolynomial.eval₂Hom (algebraMap K M) x)) :
    let phi := (groundAffineCurvePointJet p q x pivot hp hpivot hq).toRingHom
    let hphi : Function.Surjective phi :=
      groundAffineCurvePointJet_surjective p q x pivot hp hpivot hq heval
    let P := RingHom.ker (fullJetResidueMap phi)
    letI : P.IsPrime := (fullJetResidueIdeal_isMaximal phi hphi).isPrime
    0 < Module.length (Localization.AtPrime P)
      (localNormalizationDefect (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))) ∧
      Module.length (Localization.AtPrime P)
        (localNormalizationDefect (Localization.AtPrime P) (FractionRing (Localization.AtPrime P))) ≠ ⊤ := by
  let phi := (groundAffineCurvePointJet p q x pivot hp hpivot hq).toRingHom
  let hphi : Function.Surjective phi :=
    groundAffineCurvePointJet_surjective p q x pivot hp hpivot hq heval
  let P := RingHom.ker (fullJetResidueMap phi)
  letI : P.IsPrime := (fullJetResidueIdeal_isMaximal phi hphi).isPrime
  have hnontrivial : Nontrivial (localNormalizationDefect (Localization.AtPrime P)
      (FractionRing (Localization.AtPrime P))) :=
    groundAffineCurve_actualPoint_normalizationDefect_nontrivial
      p q hpirr hnot x pivot hp hpivot hq heval
  exact ⟨Module.length_pos_iff.mpr hnontrivial,
    affineCurve_point_normalizationDefect_length_ne_top_charZero p q hpirr hnot P⟩

end PfaffianDescent.Coray
