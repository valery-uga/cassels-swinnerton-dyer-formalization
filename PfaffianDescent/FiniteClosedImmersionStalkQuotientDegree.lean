import PfaffianDescent.IntrinsicFiniteCycle
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! SOURCE ONLY / UNVERIFIED157. The canonical cycle of an entire finite
closed subscheme has precisely the lengths of the actual ambient stalk
quotients as coefficients. Nilpotents and full residue degrees are retained.
This is a divisor-cycle comparison, not a line-bundle degree definition. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory AllCharacteristics
open scoped BigOperators
universe u

/-- Length of the entire quotient by the actual surjective ring-map kernel,
with its original source-ring scalar action. No radical is taken. -/
theorem surjectiveRingHom_entireKernelQuotient_length
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    Module.length R (R ⧸ RingHom.ker f) = Module.length S S := by
  let Q := R ⧸ RingHom.ker f
  have hq : Function.Surjective (algebraMap R Q) := Ideal.Quotient.mk_surjective
  have hlength : Module.length R Q = Module.length Q Q :=
    Module.length_eq_of_surjective hq
  exact hlength.trans
    (ring_length_eq_of_ringEquiv (f.quotientKerEquivOfSurjective hf))

/-- The canonical pushed-forward finite fundamental cycle has coefficient
the full O_X-module length of O_X/ker(i^#) at every actual image point. -/
theorem finiteFundamentalCycle_pushforward_apply_entireStalkQuotient
    {K : Type u} [Field K] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (g : Z ⟶ Spec (.of K)) [IsFinite g] (x : closedPoints Z) :
    pushforwardClosedCycle i (finiteSchemeFundamentalCycle g) (closedPointMap i x) =
      (Module.length (X.presheaf.stalk (i x.val))
        (X.presheaf.stalk (i x.val) ⧸ RingHom.ker (i.stalkMap x.val).hom)).toNat := by
  have hi : Function.Injective (closedPointMap i) := by
    intro x y h
    apply Subtype.ext
    exact i.isClosedEmbedding.isEmbedding.injective (congrArg Subtype.val h)
  unfold pushforwardClosedCycle
  rw [Finsupp.mapDomain_apply hi, finiteSchemeFundamentalCycle_apply]
  exact (congrArg ENat.toNat
    (surjectiveRingHom_entireKernelQuotient_length
      (i.stalkMap x.val).hom (i.stalkMap_surjective x.val))).symm

/-- Points outside the whole finite closed subscheme have coefficient zero. -/
theorem finiteFundamentalCycle_pushforward_apply_off_range
    {K : Type u} [Field K] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (g : Z ⟶ Spec (.of K)) [IsFinite g]
    (y : closedPoints X) (hy : y ∉ Set.range (closedPointMap i)) :
    pushforwardClosedCycle i (finiteSchemeFundamentalCycle g) y = 0 := by
  unfold pushforwardClosedCycle
  exact Finsupp.mapDomain_of_notMem_range _ _ hy

/-- The entire ambient stalk quotient has finite composition length, so
the cycle's ENat.toNat coefficients retain the whole finite length. -/
theorem finiteClosedImmersion_entireStalkQuotient_isFiniteLength
    {K : Type u} [Field K] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (g : Z ⟶ Spec (.of K)) [IsFinite g] (x : Z) :
    IsFiniteLength (X.presheaf.stalk (i x))
      (X.presheaf.stalk (i x) ⧸ RingHom.ker (i.stalkMap x).hom) := by
  letI : IsAffine Z := isAffine_of_isAffineHom g
  letI := finiteSchemeCoefficientAlgebra g
  letI : Module.Finite K Γ(Z, ⊤) := finiteSchemeCoefficient_finite g
  letI : IsArtinianRing Γ(Z, ⊤) := isArtinian_of_tower K inferInstance
  let q : PrimeSpectrum Γ(Z, ⊤) := Z.isoSpec.hom x
  letI : IsArtinianRing (Localization.AtPrime q.asIdeal) :=
    IsArtinianRing.localization_artinian q.asIdeal.primeCompl _
  letI : IsArtinianRing ((Spec (.of Γ(Z, ⊤))).presheaf.stalk q) :=
    (Spec.stalkIso (.of Γ(Z, ⊤)) q).commRingCatIsoToRingEquiv.symm.isArtinianRing
  letI : IsArtinianRing (Z.presheaf.stalk x) :=
    (asIso (Z.isoSpec.hom.stalkMap x)).commRingCatIsoToRingEquiv.isArtinianRing
  apply Module.length_ne_top_iff.mp
  rw [surjectiveRingHom_entireKernelQuotient_length
    (i.stalkMap x).hom (i.stalkMap_surjective x)]
  exact Module.length_ne_top

/-- The canonical entire-quotient cycle has native degree equal to the
coordinate-algebra rank; the structure maps themselves are compared. -/
theorem finiteFundamentalCycle_pushforward_degree_eq_nativeRank
    {K : Type u} [Field K] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (pi : X ⟶ Spec (.of K))
    (g : Z ⟶ Spec (.of K)) [IsFinite g] (hbase : i ≫ pi = g) :
    EffectiveZeroCycle.degree pi
      (pushforwardClosedCycle i (finiteSchemeFundamentalCycle g)) = finiteSchemeRank g := by
  rw [degree_pushforwardClosedCycle, hbase]
  exact finiteSchemeFundamentalCycle_degree g

/-- An explicit weighted sum of the entire ambient stalk quotient lengths.
The weights are the SAME ambient scheme's actual full residue degrees.
Finiteness of the indexing set follows internally from the finite scheme. -/
theorem finiteClosedImmersion_entireStalkQuotient_weighted_sum_eq_nativeRank
    {K : Type u} [Field K] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (pi : X ⟶ Spec (.of K))
    (g : Z ⟶ Spec (.of K)) [IsFinite g] (hbase : i ≫ pi = g) :
    letI := finiteScheme_isArtinian g
    letI : Fintype (closedPoints Z) := Fintype.ofFinite _
    (∑ x : closedPoints Z,
      (Module.length (X.presheaf.stalk (i x.val))
        (X.presheaf.stalk (i x.val) ⧸ RingHom.ker (i.stalkMap x.val).hom)).toNat *
          pi.residueDegree (i x.val)) = finiteSchemeRank g := by
  classical
  letI := finiteScheme_isArtinian g
  letI : Fintype (closedPoints Z) := Fintype.ofFinite _
  calc
    _ = ∑ x : closedPoints Z,
        (Module.length (Z.presheaf.stalk x.val) (Z.presheaf.stalk x.val)).toNat *
          g.residueDegree x.val := by
      apply Finset.sum_congr rfl
      intro x _
      haveI : IsIso (i.residueFieldMap x.val) :=
        isIso_residueFieldMap_of_surjectiveOnStalks i x.val
      have hres := residueDegree_comp_of_residueFieldMap_isIso i pi x.val
      rw [hbase] at hres
      exact congrArg₂ Nat.mul
        (congrArg ENat.toNat (surjectiveRingHom_entireKernelQuotient_length
          (i.stalkMap x.val).hom (i.stalkMap_surjective x.val))) hres.symm
    _ = EffectiveZeroCycle.degree g (finiteSchemeFundamentalCycle g) :=
      (fundamentalZeroCycle_degree_eq_sum g).symm
    _ = finiteSchemeRank g := finiteSchemeFundamentalCycle_degree g

end PfaffianDescent

