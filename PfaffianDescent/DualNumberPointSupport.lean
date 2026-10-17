import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-! Removing the square-zero direction of a dual-number point does not
change its actual topological support. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

theorem dualNumber_fst_spec_surjective
    {L : Type u} [Field L] :
    Function.Surjective (Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.fstHom L L L).toRingHom)) := by
  let f : DualNumber L →+* L := (TrivSqZeroExt.fstHom L L L).toRingHom
  have hker : RingHom.ker f ≤ nilradical (DualNumber L) := by
    intro x hx
    apply mem_nilradical.mpr
    apply TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst.mpr
    have hx0 : x.fst = 0 := hx
    rw [hx0]
    exact ⟨1, by simp⟩
  have h := PrimeSpectrum.isHomeomorph_comap f
    (fun x => ⟨1, by decide, ⟨TrivSqZeroExt.inl x, by simp [f]⟩⟩) hker
  change Function.Surjective (PrimeSpectrum.comap f)
  exact h.surjective

theorem dualNumber_point_range_eq_residue_range
    {L : Type u} [Field L] {X : Scheme.{u}}
    (i : Spec (.of L) ⟶ X) (j : Spec (.of (DualNumber L)) ⟶ X)
    (hfac : Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.fstHom L L L).toRingHom) ≫ j = i) :
    Set.range j = Set.range i := by
  let red := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom L L L).toRingHom)
  have hred : Function.Surjective red := dualNumber_fst_spec_surjective
  have hpoint (x : Spec (.of L)) : j (red x) = i x := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun f => f x) hfac
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hred y
    exact ⟨z, (hpoint z).symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨red z, hpoint z⟩

end PfaffianDescent
