import AllCharacteristics.CubicPencilJacobianClosedImage
import AllCharacteristics.HypersurfaceJacobianSmooth
import AllCharacteristics.ProjectivePoints

/-! SOURCE ONLY / UNVERIFIED. The omitted projective derivative locus gives
actual chart Jacobian covers, hence actual smoothness. The final pencil export
derives emptiness internally; it assumes no Jacobian-cover certificate. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory MvPolynomial
open HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k]

/-- Generic intermediate criterion, proved with actual maximal chart ideals
and the Euler identity. The distinguished partial is recovered without
inverting3, so characteristic3 is included. -/
theorem cubicJacobianScheme_isEmpty_implies_smooth
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hempty : IsEmpty (scheme (cubicJacobianIdeal p hp))) :
    Smooth (hypersurfaceToBase p hp) := by
  classical
  apply smooth_hypersurface_of_chart_pderiv_span p hp
  intro j
  by_contra hspan
  let I := equationIdeal p hp
  let D : Ideal (ChartRing I j) := Ideal.span (Set.range (chartPDeriv p hp j))
  obtain ⟨Q, hQ, hDQ⟩ := Ideal.exists_le_maximal D hspan
  letI : Q.IsMaximal := hQ
  let L := ChartRing I j ⧸ Q
  letI : Field L := Ideal.Quotient.field Q
  let e : ChartRing I j →+* L := Ideal.Quotient.mk Q
  let f : k →+* L := e.comp (chartBaseMap I j)
  let y : Fin 4 → L := fun a => e (chartCoordinate I j a)
  have hyj : y j = 1 := by simp only [y, chartCoordinate_self, map_one]
  have hy : y ≠ 0 := by
    intro hzero
    have hz := congrFun hzero j
    exact one_ne_zero (by simpa only [hyj, Pi.zero_apply] using hz)
  have hey : p.eval₂ f y = 0 := by
    have hz := congrArg e (eval₂_chartCoordinate_eq_zero I j p hp
      (Ideal.subset_span (Set.mem_singleton p)))
    rw [MvPolynomial.hom_eval₂, map_zero] at hz
    exact hz
  have hret : ∀ a : Fin 4, a ≠ j → (pderiv a p).eval₂ f y = 0 := by
    intro a haj
    have hmem : chartPDeriv p hp j ⟨a, haj⟩ ∈ Q :=
      hDQ (Ideal.subset_span ⟨⟨a, haj⟩, rfl⟩)
    have hz : e (chartPDeriv p hp j ⟨a, haj⟩) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    change e ((pderiv a p).eval₂ (chartBaseMap I j) (chartCoordinate I j)) = 0 at hz
    rw [MvPolynomial.hom_eval₂] at hz
    exact hz
  have heuler : (∑ a : Fin 4, y a * (pderiv a p).eval₂ f y) = 0 := by
    calc
      (∑ a : Fin 4, y a * (pderiv a p).eval₂ f y) =
          (∑ a : Fin 4, X a * pderiv a p).eval₂ f y := by simp
      _ = (3 • p).eval₂ f y := by rw [hp.sum_X_mul_pderiv]
      _ = 0 := by simp [hey]
  have hsum : (∑ a : Fin 4, y a * (pderiv a p).eval₂ f y) =
      y j * (pderiv j p).eval₂ f y := by
    apply Finset.sum_eq_single j
    · intro a _ haj
      rw [hret a haj, mul_zero]
    · simp
  have hj : (pderiv j p).eval₂ f y = 0 := by
    rw [hsum, hyj, one_mul] at heuler
    exact heuler
  have hderiv : ∀ a : Fin 4, (pderiv a p).eval₂ f y = 0 := by
    intro a
    by_cases haj : a = j
    · simpa only [haj] using hj
    · exact hret a haj
  let J := cubicJacobianIdeal p hp
  have hI : I.toIdeal ≤ RingHom.ker (MvPolynomial.eval₂Hom f y) := by
    apply Ideal.span_le.mpr
    rintro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact hey
  have hpartials : ∀ a : Fin 4,
      (equationIdeal (pderiv a p) hp.pderiv).toIdeal ≤
        RingHom.ker (MvPolynomial.eval₂Hom f y) := by
    intro a
    apply Ideal.span_le.mpr
    rintro b hb
    obtain rfl := Set.mem_singleton_iff.mp hb
    exact hderiv a
  have hJ : J.toIdeal ≤ RingHom.ker (MvPolynomial.eval₂Hom f y) := by
    simp only [J, cubicJacobianIdeal, HomogeneousIdeal.toIdeal_sup,
      HomogeneousIdeal.toIdeal_iSup]
    exact sup_le hI (iSup_le hpartials)
  obtain ⟨q, hq⟩ := point_of_coordinates J f y hy (fun a ha => hJ ha)
  letI : IsEmpty (scheme J) := hempty
  exact isEmptyElim (q (IsLocalRing.closedPoint L))

/-- Literal derivative-image proof of generic smoothness. No universal
smooth-parameter open, generic-smoothness theorem or closedness certificate
is used in this final proof. -/
theorem cubicPencil_map_smooth_via_projective_derivative_image
    {K : Type u} [Field K] (a : Polynomial k →+* K) (ha : Function.Injective a)
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) (hg0 : g ≠ 0)
    [Smooth (hypersurfaceToBase g hg)] :
    Smooth (hypersurfaceToBase ((cubicPencil p g).map a)
      ((cubicPencil_isHomogeneous hp hg).map a)) :=
  cubicJacobianScheme_isEmpty_implies_smooth _ _
    (cubicPencil_mappedJacobianScheme_isEmpty a ha p g hp hg hg0)

end AllCharacteristics
