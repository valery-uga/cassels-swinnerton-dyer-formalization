import AllCharacteristics.NilpotentPrescribedIdealGeneration
import Mathlib.RingTheory.Smooth.Quotient

/-! SOURCE ONLY167. Lift generators INSIDE a given flat embedded deformation.
All equality assertions concern its original ENTIRE ideal J. Upstairs
regularity is not asserted; it requires an independent regularity lift. -/
namespace AllCharacteristics
universe u v w

/-- The original quotient's GIVEN flatness supplies the whole-ideal
intersection identity, without ambient flatness or a regular pair premise. -/
theorem quotient_flat_baseIdeal_inf_eq_mul167
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal R) (J : Ideal A) [Module.Flat R (A ⧸ J)] :
    I.map (algebraMap R A) ⊓ J = I.map (algebraMap R A) * J := by
  let f := (Ideal.Quotient.mkₐ R J).toLinearMap
  have hker : f.ker = J.restrictScalars R := by
    ext x
    change Ideal.Quotient.mk J x = 0 ↔ x ∈ J
    exact Ideal.Quotient.eq_zero_iff_mem
  have hright : I • f.ker =
      (I.map (algebraMap R A) * J).restrictScalars R := by
    rw [hker, ← Ideal.smul_restrictScalars I J, Ideal.smul_eq_mul]
  have hmodule := LinearMap.ker_inf_smul_top_eq_smul_of_flat I f
    Ideal.Quotient.mk_surjective
  have hre : (J ⊓ I.map (algebraMap R A)).restrictScalars R =
      (I.map (algebraMap R A) * J).restrictScalars R := by
    calc
      (J ⊓ I.map (algebraMap R A)).restrictScalars R =
          f.ker ⊓ I • (⊤ : Submodule R A) := by
        rw [hker, Ideal.smul_top_eq_map]
        rfl
      _ = I • f.ker := hmodule
      _ = (I.map (algebraMap R A) * J).restrictScalars R := hright
  have hwhole : J ⊓ I.map (algebraMap R A) = I.map (algebraMap R A) * J := by
    ext x
    exact Submodule.ext_iff.mp hre x
  simpa only [inf_comm] using hwhole

/-- ANY two lifts inside the prescribed ideal generate it when they
already generate its whole special-fiber ideal. Nilpotents are retained. -/
theorem prescribedIdeal_eq_span_of_nilpotent_reduction167
    {R : Type u} {A : Type v} {A₀ : Type w}
    [CommRing R] [CommRing A] [CommRing A₀] [Algebra R A]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (I : Ideal R) (hI : IsNilpotent I)
    (hker : RingHom.ker π = I.map (algebraMap R A))
    (J : Ideal A) [Module.Flat R (A ⧸ J)]
    (f g : A) (hf : f ∈ J) (hg : g ∈ J)
    (hmap : J.map π = Ideal.span ({π f, π g} : Set A₀)) :
    J = Ideal.span ({f, g} : Set A) := by
  have hL : Ideal.span ({f, g} : Set A) ≤ J := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hxf | hxg
    · exact hxf.symm ▸ hf
    · exact (Set.mem_singleton_iff.mp hxg).symm ▸ hg
  have hnil : IsNilpotent (RingHom.ker π) := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, ?_⟩
    rw [hker, ← Ideal.map_pow, hn]
    simp only [Ideal.zero_eq_bot, Ideal.map_bot]
  have hLmap : (Ideal.span ({f, g} : Set A)).map π =
      Ideal.span ({π f, π g} : Set A₀) := by
    rw [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  apply ideal_eq_of_same_nilpotent_reduction167 π hπ _ J hL
    (hmap.trans hLmap.symm) hnil
  rw [hker]
  exact quotient_flat_baseIdeal_inf_eq_mul167 I J

/-- Choose lifts of the original reduced generators inside the original
prescribed ideal, and prove equality with that entire ideal. No presentation
of the prescribed ideal is supplied as a hypothesis. -/
theorem exists_prescribedIdeal_pair_lifts_of_nilpotent_reduction167
    {R : Type u} {A : Type v} {A₀ : Type w}
    [CommRing R] [CommRing A] [CommRing A₀] [Algebra R A]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (I : Ideal R) (hI : IsNilpotent I)
    (hker : RingHom.ker π = I.map (algebraMap R A))
    (J : Ideal A) [Module.Flat R (A ⧸ J)] (f₀ g₀ : A₀)
    (hmap : J.map π = Ideal.span ({f₀, g₀} : Set A₀)) :
    ∃ f g : A, f ∈ J ∧ g ∈ J ∧ π f = f₀ ∧ π g = g₀ ∧
      J = Ideal.span ({f, g} : Set A) := by
  have hf₀ : f₀ ∈ J.map π := by
    rw [hmap]
    exact Ideal.subset_span (by simp)
  have hg₀ : g₀ ∈ J.map π := by
    rw [hmap]
    exact Ideal.subset_span (by simp)
  obtain ⟨f, hf, hff⟩ := (Ideal.mem_map_iff_of_surjective π hπ).mp hf₀
  obtain ⟨g, hg, hgg⟩ := (Ideal.mem_map_iff_of_surjective π hπ).mp hg₀
  refine ⟨f, g, hf, hg, hff, hgg, ?_⟩
  apply prescribedIdeal_eq_span_of_nilpotent_reduction167 π hπ I hI hker J f g hf hg
  simpa only [hff, hgg] using hmap

end AllCharacteristics
