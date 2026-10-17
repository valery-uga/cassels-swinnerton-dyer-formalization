import AllCharacteristics.PrescribedSmoothPointLiteralSmoothing
import AllCharacteristics.CubicSingularPointReduction
import AllCharacteristics.HypersurfaceJacobianSmooth
import AllCharacteristics.ClosedPointAlgebra

/-! SOURCE ONLY / UNVERIFIED. Literal prop:smoothing proof method over
the actual Laurent-series field. The only smooth-cubic input is the stated
SmoothCubicZeroCyclePointFor k((t)); no Ma or replacement algebra is assumed. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory IsLocalRing
open HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The singular-point lemma supplies either a section or an actual point of
the ORIGINAL surface smooth locus over the SAME finite extension L. A Jacobian
existence theorem is used here to CHOOSE q, before the prescribed-q lift; that
q is then kept unchanged by all lifting and generic-cycle constructions. -/
theorem originalCubic_section_or_smoothPoint_same_extension
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (x : Fin 4 → L) (hx : x ≠ 0)
    (heval : p.eval₂ (algebraMap k L) x = 0) :
    (∃ r : Spec (.of k) ⟶ hypersurface p hp,
      r ≫ hypersurfaceToBase p hp = 𝟙 _) ∨
      ∃ q : Spec (.of L) ⟶ hypersurface p hp,
        q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
        q (closedPoint L) ∈ (hypersurfaceToBase p hp).smoothLocus := by
  obtain hground | ⟨v, hv⟩ :=
    cubic_point_or_smooth_extension_point p hp hdegree x hx heval
  · left
    obtain ⟨y, hy, hey⟩ := hground
    obtain ⟨r, hr⟩ := hypersurface_point_of_coordinates (RingHom.id k) p hp y hy hey
    exact ⟨r, by simpa using hr⟩
  · right
    obtain ⟨hv0, hve, hderiv⟩ := hv
    have hve' : p.eval₂ (algebraMap k L) v = 0 := by
      rw [MvPolynomial.eval₂_eq_eval_map]
      exact hve
    have hderiv' : ∃ j : Fin 4, (MvPolynomial.pderiv j p).eval₂ (algebraMap k L) v ≠ 0 := by
      obtain ⟨j, hj⟩ := hderiv
      refine ⟨j, ?_⟩
      rw [MvPolynomial.eval₂_eq_eval_map]
      simpa only [MvPolynomial.pderiv_map] using hj
    exact exists_hypersurface_point_mem_smoothLocus_of_pderiv
      p hp (algebraMap k L) v hv0 hve' hderiv'

/-- Exact literal smoothing proposition: arbitrary original cubic, including
zero equation, reducible or singular cubics, imperfect/finite fields and
inseparable support residue extensions. -/
theorem literalLaurentPencil_smoothing
    {k : Type u} [Field k]
    (smoothGeneric : SmoothCubicZeroCyclePointFor (LaurentSeries k))
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ r : Spec (.of k) ⟶ hypersurface p hp,
      r ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  classical
  by_cases hp0 : p = 0
  · have he : p.eval₂ (RingHom.id k) (Pi.single (0 : Fin 4) 1) = 0 := by
      simp [hp0]
    have hx : (Pi.single (0 : Fin 4) (1 : k)) ≠ 0 := by
      intro h
      have h0 := congrFun h 0
      simpa using h0
    obtain ⟨r, hr⟩ := hypersurface_point_of_coordinates (RingHom.id k) p hp _ hx he
    exact ⟨r, by simpa using hr⟩
  · let f := hypersurfaceToBase p hp
    obtain ⟨x, _, hcop⟩ := ZeroCycle.exists_coprime_degree f z hz
    let L := (hypersurface p hp).residueField x.1
    letI : Algebra k L := pointAlgebra f x.1
    letI : Module.Finite k L := closedPoint_moduleFinite f x
    have hdegree : Nat.Coprime (Module.finrank k L) 3 := by
      rw [closedPoint_finrank_eq_residueDegree f x]
      exact hcop
    obtain ⟨v, hv, he⟩ := hypersurface_residueField_coordinates p hp x.1
    obtain hground | ⟨q, hq, hsm⟩ :=
      originalCubic_section_or_smoothPoint_same_extension p hp hdegree v hv he
    · exact hground
    · exact originalSmoothPoint_section_of_literalLaurentPencil
        smoothGeneric p hp hp0 q hq hsm hdegree

end AllCharacteristics
