import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Nilpotent.Lemmas

/-! SOURCE ONLY / UNVERIFIED176. Whole support and open factorization
from an ACTUAL nilpotent coefficient fiber; no support certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

lemma nilpotentIdeal_le_nilradical176
    {B : Type u} [CommRing B] (I : Ideal B) (hI : IsNilpotent I) :
    I ≤ nilradical B := by
  obtain ⟨n, hn⟩ := hI
  intro x hx
  apply mem_nilradical.mpr
  refine ⟨n, ?_⟩
  have hxpow := Ideal.pow_mem_pow hx n
  rw [hn] at hxpow
  exact Ideal.mem_bot.mp hxpow

/-- The actual closed coefficient fiber covers every point of the base. -/
lemma surjective_specMap_of_nilpotent_kernel176
    {B K : Type u} [CommRing B] [CommRing K]
    (b : B →+* K) (hb : Function.Surjective b)
    (hnil : IsNilpotent (RingHom.ker b)) :
    Surjective (Spec.map (CommRingCat.ofHom b)) := by
  constructor
  change Function.Surjective (PrimeSpectrum.comap b)
  rw [← Set.range_eq_univ, _root_.range_comap_of_surjective K b hb,
    PrimeSpectrum.zeroLocus_eq_univ_iff]
  exact nilpotentIdeal_le_nilradical176 (RingHom.ker b) hnil

/-- Every ACTUAL Cartesian family fiber inherits that point-surjectivity. -/
lemma surjective_cartesianFamilyFiber_of_nilpotent_kernel176
    {B K : Type u} [CommRing B] [CommRing K] {X X0 : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (b : B →+* K) (hb : Function.Surjective b)
    (hnil : IsNilpotent (RingHom.ker b))
    (d : X0 ⟶ X) (f0 : X0 ⟶ Spec (.of K))
    (H : IsPullback d f0 f (Spec.map (CommRingCat.ofHom b))) : Surjective d := by
  letI : Surjective (Spec.map (CommRingCat.ofHom b)) :=
    surjective_specMap_of_nilpotent_kernel176 b hb hnil
  exact MorphismProperty.of_isPullback H.flip
    (inferInstance : Surjective (Spec.map (CommRingCat.ofHom b)))

/-- A whole Cartesian field-point fiber forces the WHOLE deformation to
have the original point as its entire topological support. No finite/flat
assumptions are needed for this stronger support assertion. -/
lemma nilpotentCartesianFieldPoint_support176
    {B K L : Type u} [CommRing B] [CommRing K] [Field L]
    {X X0 Z : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (b : B →+* K) (hb : Function.Surjective b)
    (hnil : IsNilpotent (RingHom.ker b))
    (d : X0 ⟶ X) (f0 : X0 ⟶ Spec (.of K))
    (H0 : IsPullback d f0 f (Spec.map (CommRingCat.ofHom b)))
    (i : Z ⟶ X) (u0 : Spec (.of L) ⟶ Z) (v : Spec (.of L) ⟶ X0)
    (H : IsPullback u0 v i d) :
    ∀ z : Z, i z = d (v default) := by
  have HZ := H.paste_vert H0
  letI : Surjective u0 := surjective_cartesianFamilyFiber_of_nilpotent_kernel176
    (i ≫ f) b hb hnil u0 (v ≫ f0) HZ
  intro z
  obtain ⟨w, rfl⟩ := u0.surjective z
  have hw : w = (default : Spec (.of L)) := Subsingleton.elim _ _
  subst w
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun h => h default) H.w

/-- The SAME entire Z factors through any open neighborhood. No
restriction of Z, removal of components or support premise occurs. -/
lemma exists_open_factor_of_nilpotentCartesianFieldPoint176
    {B K L : Type u} [CommRing B] [CommRing K] [Field L]
    {X X0 Z : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (b : B →+* K) (hb : Function.Surjective b)
    (hnil : IsNilpotent (RingHom.ker b))
    (d : X0 ⟶ X) (f0 : X0 ⟶ Spec (.of K))
    (H0 : IsPullback d f0 f (Spec.map (CommRingCat.ofHom b)))
    (i : Z ⟶ X) [IsClosedImmersion i]
    (u0 : Spec (.of L) ⟶ Z) (v : Spec (.of L) ⟶ X0)
    (H : IsPullback u0 v i d) (U : X.Opens) (hU : d (v default) ∈ U) :
    ∃ iU : Z ⟶ U, iU ≫ U.ι = i ∧ IsClosedImmersion iU := by
  have hs := nilpotentCartesianFieldPoint_support176 f b hb hnil d f0 H0 i u0 v H
  have hrange : Set.range i ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [hs z]
    exact hU
  let iU := IsOpenImmersion.lift U.ι i hrange
  have hfac : iU ≫ U.ι = i := IsOpenImmersion.lift_fac U.ι i hrange
  letI : IsClosedImmersion (iU ≫ U.ι) := by rw [hfac]; infer_instance
  exact ⟨iU, hfac, IsClosedImmersion.of_comp iU U.ι⟩

/-- The named actual factor keeps the SAME entire deformation scheme Z. -/
def nilpotentCartesianFieldPoint_openFactor176
    {B K L : Type u} [CommRing B] [CommRing K] [Field L]
    {X X0 Z : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (b : B →+* K) (hb : Function.Surjective b)
    (hnil : IsNilpotent (RingHom.ker b))
    (d : X0 ⟶ X) (f0 : X0 ⟶ Spec (.of K))
    (H0 : IsPullback d f0 f (Spec.map (CommRingCat.ofHom b)))
    (i : Z ⟶ X) [IsClosedImmersion i]
    (u0 : Spec (.of L) ⟶ Z) (v : Spec (.of L) ⟶ X0)
    (H : IsPullback u0 v i d) (U : X.Opens) (hU : d (v default) ∈ U) : Z ⟶ U :=
  Classical.choose (exists_open_factor_of_nilpotentCartesianFieldPoint176
    f b hb hnil d f0 H0 i u0 v H U hU)

/-- Literal factorization equality into the original ambient scheme. -/
lemma nilpotentCartesianFieldPoint_openFactor176_fac
    {B K L : Type u} [CommRing B] [CommRing K] [Field L]
    {X X0 Z : Scheme.{u}}
    (f : X ⟶ Spec (.of B)) (b : B →+* K) (hb : Function.Surjective b)
    (hnil : IsNilpotent (RingHom.ker b))
    (d : X0 ⟶ X) (f0 : X0 ⟶ Spec (.of K))
    (H0 : IsPullback d f0 f (Spec.map (CommRingCat.ofHom b)))
    (i : Z ⟶ X) [IsClosedImmersion i]
    (u0 : Spec (.of L) ⟶ Z) (v : Spec (.of L) ⟶ X0)
    (H : IsPullback u0 v i d) (U : X.Opens) (hU : d (v default) ∈ U) :
    nilpotentCartesianFieldPoint_openFactor176 f b hb hnil d f0 H0 i u0 v H U hU ≫ U.ι = i :=
  (Classical.choose_spec (exists_open_factor_of_nilpotentCartesianFieldPoint176
    f b hb hnil d f0 H0 i u0 v H U hU)).1

end PfaffianDescent
