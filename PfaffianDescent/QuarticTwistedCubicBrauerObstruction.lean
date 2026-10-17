import PfaffianDescent.QuarticTwistedCubicCocycle

/-!
# The coprime scalar-obstruction calculation for twisted-cubic descent

A form of the projective line has a scalar obstruction after its projective
descent datum is lifted to binary matrices.  Determinants make this
obstruction two-torsion.  The cubic symmetric-power representation makes it
three-torsion when the ambient `P³` descent datum is split.  The elementary
calculation below is the common `2`--`3` torsion step: a scalar two-cochain
which is both a square and a cube coboundary is itself a coboundary.

The remaining geometric connection is the construction of the relevant
projective cocycle from a geometrically twisted cubic, followed by Hilbert 90
for the resulting linear descent datum.
-/

namespace PfaffianDescent
namespace QuarticNet

universe u v w

variable {A : Type u} [CommGroup A] {G : Type v} [Group G]

/-- The scalar coboundary of a one-cochain for a specified action of `G`. -/
def scalarCoboundary (action : G → A →* A) (u : G → A) (g h : G) : A :=
  u g * action g (u h) * (u (g * h))⁻¹

/-- A scalar two-cochain is a coboundary if it has the displayed form. -/
def ScalarTwoCochainIsCoboundary (action : G → A →* A) (d : G → G → A) : Prop :=
  ∃ u : G → A, ∀ g h, d g h = scalarCoboundary action u g h

theorem scalarCoboundary_div (action : G → A →* A) (u v : G → A) (g h : G) :
    scalarCoboundary action (fun x => u x / v x) g h =
      scalarCoboundary action u g h / scalarCoboundary action v g h := by
  simp only [scalarCoboundary, map_div, inv_div]
  rw [div_mul_div_comm]
  conv_rhs => rw [mul_div_mul_comm]
  simp only [div_eq_mul_inv, inv_inv]
  rw [mul_left_cancel_iff]
  exact mul_comm _ _

/-- The scalar part of the twisted-cubic descent obstruction vanishes once
both its determinant-square and its symmetric-cube are coboundaries. -/
theorem scalarTwoCochain_isCoboundary_of_square_and_cube
    (action : G → A →* A) (d : G → G → A)
    (h2 : ScalarTwoCochainIsCoboundary action (fun g h => d g h ^ 2))
    (h3 : ScalarTwoCochainIsCoboundary action (fun g h => d g h ^ 3)) :
    ScalarTwoCochainIsCoboundary action d := by
  obtain ⟨u, hu⟩ := h2
  obtain ⟨v, hv⟩ := h3
  refine ⟨fun g => v g / u g, ?_⟩
  intro g h
  have hu' : d g h ^ 2 = scalarCoboundary action u g h := by
    simpa using hu g h
  have hv' : d g h ^ 3 = scalarCoboundary action v g h := by
    simpa using hv g h
  calc
    d g h = d g h ^ 3 / d g h ^ 2 := by
      rw [div_eq_mul_inv]
      simpa using (pow_sub (d g h) (show 2 ≤ 3 by omega))
    _ = scalarCoboundary action v g h / scalarCoboundary action u g h := by
      rw [hv', hu']
    _ = scalarCoboundary action (fun x => v x / u x) g h :=
      (scalarCoboundary_div action v u g h).symm

end QuarticNet
end PfaffianDescent

namespace PfaffianDescent
namespace QuarticNet

open Matrix
open scoped MatrixGroups

universe u v

variable {L : Type u} [Field L] {G : Type v} [Group G]

/-- The action on nonzero scalars induced by a field automorphism. -/
noncomputable def unitFieldAction (rho : G →* L ≃+* L) (g : G) : Lˣ →* Lˣ :=
  Units.map (rho g).toRingHom.toMonoidHom

namespace ProjectiveCocycle

/-- A choice of matrix representatives for a projective cocycle. -/
structure Lift {n : ℕ} {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) n rho) where
  toFun : G → GL (Fin n) L
  projectivize : ∀ g, Matrix.ProjGenLinGroup.mk (toFun g) = c g

/-- Every projective cocycle has matrix representatives. -/
noncomputable def chooseLift {n : ℕ} {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) n rho) : Lift c where
  toFun g := Quotient.out (c g)
  projectivize g := Quotient.out_eq (c g)

lemma Lift.projective_mul {n : ℕ} {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) n rho) (l : Lift c) (g h : G) :
    Matrix.ProjGenLinGroup.mk
      (l.toFun g * Matrix.GeneralLinearGroup.map (rho g).toRingHom (l.toFun h)) =
        Matrix.ProjGenLinGroup.mk (l.toFun (g * h)) := by
  rw [Matrix.ProjGenLinGroup.mk.map_mul, l.projectivize g,
    ← Matrix.ProjGenLinGroup.map_mk, l.projectivize h, l.projectivize (g * h)]
  simpa [projectiveFieldAction] using (c.map_mul' g h).symm

/-- The scalar discrepancy between matrix representatives of a projective
cocycle and their product law. -/
noncomputable def Lift.defect {n : ℕ} {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) n rho) (l : Lift c) (g h : G) : Lˣ :=
  (Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp (l.projective_mul c g h)).choose

lemma Lift.mul_scalar_defect {n : ℕ} {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) n rho) (l : Lift c) (g h : G) :
    (l.toFun g * Matrix.GeneralLinearGroup.map (rho g).toRingHom (l.toFun h)) *
      Matrix.GeneralLinearGroup.scalar (Fin n) (l.defect c g h) = l.toFun (g * h) :=
  (Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp (l.projective_mul c g h)).choose_spec

/-- Determinants make the scalar obstruction of a binary projective cocycle
a square coboundary. -/
lemma Lift.defect_square_isCoboundary {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) 2 rho) (l : Lift c) :
    ScalarTwoCochainIsCoboundary (unitFieldAction rho)
      (fun g h => l.defect c g h ^ 2) := by
  refine ⟨fun g => (Matrix.GeneralLinearGroup.det (l.toFun g))⁻¹, ?_⟩
  intro g h
  have hd := congrArg Matrix.GeneralLinearGroup.det (l.mul_scalar_defect c g h)
  simp only [map_mul, Matrix.GeneralLinearGroup.map_det,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hd
  change l.defect c g h ^ 2 = scalarCoboundary (unitFieldAction rho)
    (fun g => (Matrix.GeneralLinearGroup.det (l.toFun g))⁻¹) g h
  simp only [scalarCoboundary, unitFieldAction, map_inv, inv_inv]
  calc
    l.defect c g h ^ 2 =
        (Matrix.GeneralLinearGroup.det (l.toFun g) *
          Units.map (rho g).toRingHom.toMonoidHom
            (Matrix.GeneralLinearGroup.det (l.toFun h)))⁻¹ *
          Matrix.GeneralLinearGroup.det (l.toFun (g * h)) := by
      rw [eq_comm]
      exact (inv_mul_eq_iff_eq_mul).mpr hd.symm
    _ = (Matrix.GeneralLinearGroup.det (l.toFun g))⁻¹ *
          (Units.map (rho g).toRingHom.toMonoidHom
            (Matrix.GeneralLinearGroup.det (l.toFun h)))⁻¹ *
          Matrix.GeneralLinearGroup.det (l.toFun (g * h)) := by
      rw [_root_.mul_inv_rev]
      rw [mul_comm (Units.map (rho g).toRingHom.toMonoidHom
        (Matrix.GeneralLinearGroup.det (l.toFun h)))⁻¹]

end ProjectiveCocycle
end QuarticNet
end PfaffianDescent

namespace PfaffianDescent.QuarticNet.ProjectiveCocycle

open Matrix
open scoped MatrixGroups

universe u v

variable {L : Type u} [Field L] {G : Type v} [Group G]

/-- Applying the symmetric-cube representation to a binary lift carries its
scalar defect to the third power. -/
lemma Lift.symmetricCube_mul_scalar_defect {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) 2 rho) (l : Lift c) (g h : G) :
    (symmetricCubeGL (l.toFun g) *
      Matrix.GeneralLinearGroup.map (rho g).toRingHom (symmetricCubeGL (l.toFun h))) *
        Matrix.GeneralLinearGroup.scalar (Fin 4) (l.defect c g h ^ 3) =
      symmetricCubeGL (l.toFun (g * h)) := by
  have h := congrArg symmetricCubeGL (l.mul_scalar_defect c g h)
  simp only [map_mul, symmetricCubeGL_scalar] at h
  rw [← symmetricCubeGL_map] at h
  exact h

end PfaffianDescent.QuarticNet.ProjectiveCocycle

namespace PfaffianDescent.QuarticNet

open Matrix
open scoped MatrixGroups

universe u v

variable {L : Type u} [Field L] {G : Type v} [Group G]

/-- A matrix representative of the ambient projective coboundary. -/
noncomputable def ambientCoboundary (rho : G →* L ≃+* L)
    (X : GL (Fin 4) L) (g : G) : GL (Fin 4) L :=
  X⁻¹ * Matrix.GeneralLinearGroup.map (rho g).toRingHom X

lemma ambientCoboundary_mul (rho : G →* L ≃+* L)
    (X : GL (Fin 4) L) (g h : G) :
    ambientCoboundary rho X g *
      Matrix.GeneralLinearGroup.map (rho g).toRingHom (ambientCoboundary rho X h) =
        ambientCoboundary rho X (g * h) := by
  simp only [ambientCoboundary, map_mul, map_inv]
  have hmap : Matrix.GeneralLinearGroup.map (rho g).toRingHom
      (Matrix.GeneralLinearGroup.map (rho h).toRingHom X) =
        Matrix.GeneralLinearGroup.map (rho (g * h)).toRingHom X := by
    apply Units.ext
    change ((X : Matrix (Fin 4) (Fin 4) L).map (rho h).toRingHom).map (rho g).toRingHom =
      (X : Matrix (Fin 4) (Fin 4) L).map (rho (g * h)).toRingHom
    rw [Matrix.map_map]
    rw [rho.map_mul]
    rfl
  rw [hmap]
  rw [mul_assoc]
  rw [← mul_assoc (Matrix.GeneralLinearGroup.map (rho g).toRingHom X)
    ((Matrix.GeneralLinearGroup.map (rho g).toRingHom X)⁻¹)
    (Matrix.GeneralLinearGroup.map (rho (g * h)).toRingHom X)]
  rw [mul_inv_cancel, one_mul]
  rw [rho.map_mul]

end PfaffianDescent.QuarticNet

namespace PfaffianDescent.QuarticNet.ProjectiveCocycle

open Matrix
open scoped MatrixGroups

universe u v

variable {L : Type u} [Field L] {G : Type v} [Group G]

lemma symmetricCube_projective_eq_ambient {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) 2 rho) (l : Lift c)
    (x : PGL(Fin 4, L))
    (hx : ∀ g, symmetricCube c g = x⁻¹ * projectiveFieldAction 4 rho g x)
    (g : G) :
    Matrix.ProjGenLinGroup.mk (symmetricCubeGL (l.toFun g)) =
      Matrix.ProjGenLinGroup.mk
        (ambientCoboundary rho (Quotient.out x) g) := by
  have hX : Matrix.ProjGenLinGroup.mk (Quotient.out x) = x := Quotient.out_eq x
  calc
    Matrix.ProjGenLinGroup.mk (symmetricCubeGL (l.toFun g)) =
        symmetricCubePGL (Matrix.ProjGenLinGroup.mk (l.toFun g)) :=
      (symmetricCubePGL_mk (l.toFun g)).symm
    _ = symmetricCubePGL (c g) := by rw [l.projectivize g]
    _ = x⁻¹ * projectiveFieldAction 4 rho g x := hx g
    _ = Matrix.ProjGenLinGroup.mk (Quotient.out x)⁻¹ *
        projectiveFieldAction 4 rho g (Matrix.ProjGenLinGroup.mk (Quotient.out x)) := by
      exact congrArg (fun z : PGL(Fin 4, L) => z⁻¹ * projectiveFieldAction 4 rho g z) hX.symm
    _ = Matrix.ProjGenLinGroup.mk ((Quotient.out x)⁻¹) *
        Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.map (rho g).toRingHom (Quotient.out x)) := by
      rw [map_inv, projectiveFieldAction, ← Matrix.ProjGenLinGroup.map_mk]
    _ = Matrix.ProjGenLinGroup.mk
        ((Quotient.out x)⁻¹ *
          Matrix.GeneralLinearGroup.map (rho g).toRingHom (Quotient.out x)) := by
      rw [Matrix.ProjGenLinGroup.mk.map_mul]
    _ = Matrix.ProjGenLinGroup.mk
        (ambientCoboundary rho (Quotient.out x) g) := rfl

/-- The scalar relating the symmetric-cube lift to an ambient matrix
coboundary. -/
noncomputable def symmetricCubeCoboundaryDefect {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) 2 rho) (l : Lift c)
    (x : PGL(Fin 4, L))
    (hx : ∀ g, symmetricCube c g = x⁻¹ * projectiveFieldAction 4 rho g x)
    (g : G) : Lˣ :=
  (Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp
    (symmetricCube_projective_eq_ambient c l x hx g)).choose

lemma symmetricCube_mul_scalar_coboundaryDefect {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) 2 rho) (l : Lift c)
    (x : PGL(Fin 4, L))
    (hx : ∀ g, symmetricCube c g = x⁻¹ * projectiveFieldAction 4 rho g x)
    (g : G) :
    symmetricCubeGL (l.toFun g) *
      Matrix.GeneralLinearGroup.scalar (Fin 4)
        (symmetricCubeCoboundaryDefect c l x hx g) =
      ambientCoboundary rho (Quotient.out x) g :=
  (Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp
    (symmetricCube_projective_eq_ambient c l x hx g)).choose_spec

lemma scalarGL4_injective : Function.Injective
    (Matrix.GeneralLinearGroup.scalar (Fin 4) : Lˣ → GL (Fin 4) L) := by
  intro u v huv
  apply Units.ext
  have hmatrix : (((Matrix.GeneralLinearGroup.scalar (Fin 4)) u : GL (Fin 4) L) :
      Matrix (Fin 4) (Fin 4) L) =
      (((Matrix.GeneralLinearGroup.scalar (Fin 4)) v : GL (Fin 4) L) :
        Matrix (Fin 4) (Fin 4) L) :=
    congrArg (fun z : GL (Fin 4) L => (z : Matrix (Fin 4) (Fin 4) L)) huv
  have h := congrFun (congrFun hmatrix (0 : Fin 4)) (0 : Fin 4)
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply] using h

/-- If the cubic symmetric-power cocycle is a projective coboundary, then
the scalar obstruction of a binary lift has cubed coboundary. -/
lemma Lift.defect_cube_isCoboundary {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) 2 rho) (l : Lift c)
    (hc : (symmetricCube c).IsCoboundary) :
    ScalarTwoCochainIsCoboundary (unitFieldAction rho)
      (fun g h => l.defect c g h ^ 3) := by
  obtain ⟨x, hx⟩ := hc
  let beta : G → Lˣ := symmetricCubeCoboundaryDefect c l x hx
  let B : G → GL (Fin 4) L := fun g => symmetricCubeGL (l.toFun g)
  let R : G → GL (Fin 4) L := fun g => ambientCoboundary rho (Quotient.out x) g
  let s : G → GL (Fin 4) L := fun g => Matrix.GeneralLinearGroup.scalar (Fin 4) (beta g)
  have hB (g : G) : B g * s g = R g := by
    exact symmetricCube_mul_scalar_coboundaryDefect c l x hx g
  have hD (g h : G) :
      (B g * Matrix.GeneralLinearGroup.map (rho g).toRingHom (B h)) *
          Matrix.GeneralLinearGroup.scalar (Fin 4) (l.defect c g h ^ 3) = B (g * h) := by
    exact l.symmetricCube_mul_scalar_defect c g h
  have hR (g h : G) : R g * Matrix.GeneralLinearGroup.map (rho g).toRingHom (R h) =
      R (g * h) := ambientCoboundary_mul rho (Quotient.out x) g h
  refine ⟨beta, ?_⟩
  intro g h
  apply scalarGL4_injective
  let S : Lˣ →* GL (Fin 4) L := Matrix.GeneralLinearGroup.scalar (Fin 4)
  change S (l.defect c g h ^ 3) =
    S (scalarCoboundary (unitFieldAction rho) beta g h)
  rw [scalarCoboundary, S.map_mul, S.map_mul, S.map_inv]
  dsimp only [S, s, unitFieldAction]
  have hsmap : Matrix.GeneralLinearGroup.map (rho g).toRingHom (s h) =
      Matrix.GeneralLinearGroup.scalar (Fin 4)
        (Units.map (rho g).toRingHom.toMonoidHom (beta h)) := by
    dsimp [s]
    exact Matrix.GeneralLinearGroup.map_scalar (rho g).toRingHom (beta h)
  rw [← hsmap]
  apply (eq_mul_inv_iff_mul_eq).mpr
  refine (mul_left_cancel_iff (a := B g * Matrix.GeneralLinearGroup.map (rho g).toRingHom (B h))).mp ?_
  calc
    (B g * Matrix.GeneralLinearGroup.map (rho g).toRingHom (B h)) *
        (Matrix.GeneralLinearGroup.scalar (Fin 4) (l.defect c g h ^ 3) * s (g * h)) =
      ((B g * Matrix.GeneralLinearGroup.map (rho g).toRingHom (B h)) *
        Matrix.GeneralLinearGroup.scalar (Fin 4) (l.defect c g h ^ 3)) * s (g * h) := by
        rw [← mul_assoc]
    _ = B (g * h) * s (g * h) := by rw [hD]
    _ = R (g * h) := hB (g * h)
    _ = R g * Matrix.GeneralLinearGroup.map (rho g).toRingHom (R h) := (hR g h).symm
    _ = (B g * s g) * Matrix.GeneralLinearGroup.map (rho g).toRingHom (B h * s h) := by
      rw [hB g, hB h]
    _ = (B g * Matrix.GeneralLinearGroup.map (rho g).toRingHom (B h)) *
        (s g * Matrix.GeneralLinearGroup.map (rho g).toRingHom (s h)) := by
      calc
        (B g * s g) * Matrix.GeneralLinearGroup.map (rho g).toRingHom (B h * s h) =
          (B g * s g) *
            (Matrix.GeneralLinearGroup.map (rho g).toRingHom (B h) *
              Matrix.GeneralLinearGroup.map (rho g).toRingHom (s h)) := by rw [map_mul]
        _ = B g * (s g *
            (Matrix.GeneralLinearGroup.map (rho g).toRingHom (B h) *
              Matrix.GeneralLinearGroup.map (rho g).toRingHom (s h))) := by
              exact mul_assoc _ _ _
        _ = B g * ((s g * Matrix.GeneralLinearGroup.map (rho g).toRingHom (B h)) *
              Matrix.GeneralLinearGroup.map (rho g).toRingHom (s h)) := by
              exact congrArg (fun z => B g * z)
                (mul_assoc _ _ _).symm
        _ = B g * ((Matrix.GeneralLinearGroup.map (rho g).toRingHom (B h) * s g) *
              Matrix.GeneralLinearGroup.map (rho g).toRingHom (s h)) := by
              exact congrArg (fun z => B g * z)
                (congrArg (fun z => z * Matrix.GeneralLinearGroup.map (rho g).toRingHom (s h))
                  (Matrix.GeneralLinearGroup.scalar_commute _ _))
        _ = B g * (Matrix.GeneralLinearGroup.map (rho g).toRingHom (B h) *
              (s g * Matrix.GeneralLinearGroup.map (rho g).toRingHom (s h))) := by
              exact congrArg (fun z => B g * z) (mul_assoc _ _ _)
        _ = (B g * Matrix.GeneralLinearGroup.map (rho g).toRingHom (B h)) *
              (s g * Matrix.GeneralLinearGroup.map (rho g).toRingHom (s h)) := by
              exact (mul_assoc _ _ _).symm

/-- The determinant and symmetric-cube calculations together trivialize the
scalar obstruction of the binary projective cocycle. -/
theorem Lift.defect_isCoboundary_of_symmetricCube_isCoboundary {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) 2 rho) (l : Lift c)
    (hc : (symmetricCube c).IsCoboundary) :
    ScalarTwoCochainIsCoboundary (unitFieldAction rho) (l.defect c) :=
  scalarTwoCochain_isCoboundary_of_square_and_cube (unitFieldAction rho) (l.defect c)
    (l.defect_square_isCoboundary c) (l.defect_cube_isCoboundary c hc)

/-- A matrix-valued descent cocycle. -/
structure LinearCocycle (n : ℕ) (rho : G →* L ≃+* L) where
  toFun : G → GL (Fin n) L
  map_mul' : ∀ g h, toFun (g * h) =
    toFun g * Matrix.GeneralLinearGroup.map (rho g).toRingHom (toFun h)

/-- Adjusting a projective lift by a scalar cochain which trivializes its
defect yields an honest linear descent cocycle. -/
noncomputable def Lift.strictify {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) 2 rho) (l : Lift c)
    (u : G → Lˣ)
    (hu : ∀ g h, l.defect c g h = scalarCoboundary (unitFieldAction rho) u g h) :
    LinearCocycle (L := L) (G := G) 2 rho where
  toFun g := l.toFun g * Matrix.GeneralLinearGroup.scalar (Fin 2) (u g)
  map_mul' g h := by
    let A : GL (Fin 2) L := l.toFun g
    let B : GL (Fin 2) L := Matrix.GeneralLinearGroup.map (rho g).toRingHom (l.toFun h)
    let U : GL (Fin 2) L := Matrix.GeneralLinearGroup.scalar (Fin 2) (u g)
    let V : GL (Fin 2) L := Matrix.GeneralLinearGroup.map (rho g).toRingHom
      (Matrix.GeneralLinearGroup.scalar (Fin 2) (u h))
    let D : GL (Fin 2) L := Matrix.GeneralLinearGroup.scalar (Fin 2) (l.defect c g h)
    let W : GL (Fin 2) L := Matrix.GeneralLinearGroup.scalar (Fin 2) (u (g * h))
    have hd : (A * B) * D = l.toFun (g * h) := l.mul_scalar_defect c g h
    have hscalar : U * V = D * W := by
      let S : Lˣ →* GL (Fin 2) L := Matrix.GeneralLinearGroup.scalar (Fin 2)
      have hunit : u g * Units.map (rho g).toRingHom.toMonoidHom (u h) =
          l.defect c g h * u (g * h) := by
        rw [hu]
        simp only [scalarCoboundary, unitFieldAction, mul_assoc, inv_mul_cancel, mul_one]
      dsimp [U, V, D, W]
      rw [Matrix.GeneralLinearGroup.map_scalar]
      rw [← S.map_mul, ← S.map_mul]
      exact congrArg S hunit
    have hcomm : U * B = B * U := by
      dsimp [U]
      exact Matrix.GeneralLinearGroup.scalar_commute (u g) B
    rw [map_mul]
    change l.toFun (g * h) * W = (A * U) * (B * V)
    calc
      l.toFun (g * h) * W = ((A * B) * D) * W := by rw [hd]
      _ = (A * B) * (D * W) := by rw [mul_assoc]
      _ = (A * B) * (U * V) := by rw [hscalar]
      _ = A * (B * (U * V)) := by exact mul_assoc _ _ _
      _ = A * ((B * U) * V) := by
        exact congrArg (fun z => A * z) (mul_assoc _ _ _).symm
      _ = A * ((U * B) * V) := by
        exact congrArg (fun z => A * (z * V)) hcomm.symm
      _ = A * (U * (B * V)) := by
        exact congrArg (fun z => A * z) (mul_assoc _ _ _)
      _ = (A * U) * (B * V) := by exact (mul_assoc _ _ _).symm

lemma Lift.strictify_projectivize {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) 2 rho) (l : Lift c)
    (u : G → Lˣ)
    (hu : ∀ g h, l.defect c g h = scalarCoboundary (unitFieldAction rho) u g h)
    (g : G) :
    Matrix.ProjGenLinGroup.mk ((l.strictify c u hu).toFun g) = c g := by
  change Matrix.ProjGenLinGroup.mk
    (l.toFun g * Matrix.GeneralLinearGroup.scalar (Fin 2) (u g)) = c g
  rw [Matrix.ProjGenLinGroup.mk.map_mul, Matrix.ProjGenLinGroup.mk_scalar, mul_one,
    l.projectivize g]

/-- A linear cocycle is split when it is represented by one change of basis
after scalar transport.  Hilbert 90 is precisely the missing theorem which
establishes this condition for Galois descent data. -/
def LinearCocycle.IsCoboundary {n : ℕ} {rho : G →* L ≃+* L}
    (a : LinearCocycle (L := L) (G := G) n rho) : Prop :=
  ∃ X : GL (Fin n) L, ∀ g,
    a.toFun g = X⁻¹ * Matrix.GeneralLinearGroup.map (rho g).toRingHom X

lemma Lift.projective_isCoboundary_of_strictify_isCoboundary {rho : G →* L ≃+* L}
    (c : ProjectiveCocycle (L := L) 2 rho) (l : Lift c)
    (u : G → Lˣ)
    (hu : ∀ g h, l.defect c g h = scalarCoboundary (unitFieldAction rho) u g h)
    (h : (l.strictify c u hu).IsCoboundary) : c.IsCoboundary := by
  obtain ⟨X, hX⟩ := h
  refine ⟨Matrix.ProjGenLinGroup.mk X, ?_⟩
  intro g
  rw [← l.strictify_projectivize c u hu g, hX g]
  rw [Matrix.ProjGenLinGroup.mk.map_mul, map_inv, projectiveFieldAction,
    ← Matrix.ProjGenLinGroup.map_mk]

end PfaffianDescent.QuarticNet.ProjectiveCocycle
