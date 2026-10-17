import AllCharacteristics.SmoothSchemeRegularity
import AllCharacteristics.HypersurfaceJacobianSmooth

/-!
# Domain local rings on smooth hypersurface charts

A smooth projective hypersurface over a field has domain local rings.  The
statement here transfers that fact through the normalized affine-chart
presentation to the localizations of its chart coordinate rings.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective

universe u

/-- Localizing a normalized chart of a smooth projective hypersurface at any
prime gives a domain. -/
theorem isDomain_localization_at_hypersurface_chart_of_smooth
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] (j : Fin 4)
    (M : Ideal (ChartRing (equationIdeal p hp) j)) [M.IsPrime] :
    IsDomain (Localization.AtPrime M) := by
  let y : Spec (.of (ChartRing (equationIdeal p hp) j)) := ⟨M, inferInstance⟩
  haveI : IsDomain ((hypersurface p hp).presheaf.stalk
      (chartι (equationIdeal p hp) j y)) :=
    isDomain_stalk_of_smooth_toSpec_field (hypersurfaceToBase p hp)
      (chartι (equationIdeal p hp) j y)
  have hdomain : IsDomain ((hypersurface p hp).presheaf.stalk
      (chartι (equationIdeal p hp) j y)) := inferInstance
  haveI : IsDomain ((Spec (.of (ChartRing (equationIdeal p hp) j))).presheaf.stalk y) :=
    isDomain_of_ringEquiv hdomain
      (asIso ((chartι (equationIdeal p hp) j).stalkMap y)).commRingCatIsoToRingEquiv
  exact isDomain_of_ringEquiv inferInstance
    (Spec.stalkIso (.of (ChartRing (equationIdeal p hp) j)) y).commRingCatIsoToRingEquiv

/-- The same domain conclusion holds for a ring presented as a normalized
chart by an explicit ring equivalence. -/
theorem isDomain_localization_of_ringEquiv_hypersurface_chart
    {K : Type u} [Field K] (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [Smooth (hypersurfaceToBase p hp)] (j : Fin 4)
    {B : Type u} [CommRing B] (e : B ≃+* ChartRing (equationIdeal p hp) j)
    (M : Ideal B) [M.IsPrime] :
    IsDomain (Localization.AtPrime M) := by
  let N : Ideal (ChartRing (equationIdeal p hp) j) := Ideal.map e M
  have hcomap : Ideal.comap e N = M := by
    change Ideal.comap e (Ideal.map e M) = M
    rw [Ideal.comap_map_of_surjective e e.surjective]
    apply sup_eq_left.mpr
    intro x hx
    change e x = 0 at hx
    have hxzero : x = 0 := e.injective (by simpa using hx)
    exact hxzero ▸ M.zero_mem
  letI : N.IsPrime := by
    dsimp [N]
    apply Ideal.map_isPrime_of_surjective e.surjective
    intro x hx
    change e x = 0 at hx
    have hxzero : x = 0 := e.injective (by simpa using hx)
    exact hxzero ▸ M.zero_mem
  have hN : IsDomain (Localization.AtPrime N) :=
    isDomain_localization_at_hypersurface_chart_of_smooth p hp j N
  let l : Localization.AtPrime M ≃+* Localization.AtPrime N :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime M)
      (Localization.AtPrime N) e (by
        change Submonoid.map e.toMonoidHom M.primeCompl = N.primeCompl
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          change e x ∉ N
          intro hex
          have hxm : x ∈ Ideal.comap e N := hex
          rw [hcomap] at hxm
          exact hx hxm
        · intro hz
          change z ∉ N at hz
          obtain ⟨x, rfl⟩ := e.surjective z
          refine ⟨x, ?_, rfl⟩
          change x ∉ M
          intro hx
          exact hz (Ideal.mem_map_of_mem e hx))
  exact isDomain_of_ringEquiv hN l.symm

end HomogeneousProjective
end AllCharacteristics
