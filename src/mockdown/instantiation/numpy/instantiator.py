import operator
from pprint import pprint
from typing import Sequence
import itertools as it

import numpy as np  # type: ignore
import pandas as pd  # type: ignore
from more_itertools import flatten

from mockdown.constraint import IConstraint, ConstraintKind
from mockdown.constraint.factory import ConstraintFactory
from mockdown.instantiation.types import IConstraintInstantiator
from mockdown.instantiation.visibility import visible_pairs
from mockdown.model import IView, Attribute
from mockdown.types import NT


class NumpyConstraintInstantiator(IConstraintInstantiator[NT]):
    def __init__(self, examples: Sequence[IView[NT]]):
        self.examples = examples

        # noinspection PyTypeChecker
        self.anchor_ids = anchor_ids = np.array(sorted(examples[0].all_anchor_ids))
        # noinspection PyTypeChecker
        self.anchors = anchors = np.array(sorted(examples[0].all_anchors, key=lambda a: a.id))

        # noinspection PyPep8Naming
        N = len(anchor_ids)

        # 0. A nice index for the weirder queries...
        index = pd.MultiIndex.from_tuples(set(
            (id.view_name, id.attribute.value) for id in anchor_ids
        )).sort_values()

        # 1. Construct base matrix of all anchor pairs.
        anchor_vec = pd.Series(anchors, index=index)
        anchor_mat_np = np.zeros((N, N), dtype=object)
        for (r, c) in it.product(np.arange(0, N), np.arange(0, N)):
            # print(r,c)
            anchor_mat_np[r, c] = (anchors[r], anchors[c])
        self.anchor_mat = anchor_mat = pd.DataFrame(anchor_mat_np, columns=index, index=index)

        # 2. Encode size/position/horizontal/vertical etc as matrices.
        self.is_size_vec = anchor_vec.map(lambda a: a.id.attribute.is_size()).astype(np.int8)
        self.both_size_mat = pd.DataFrame(np.outer(self.is_size_vec, self.is_size_vec), columns=index, index=index)

        self.is_pos_vec = anchor_vec.map(lambda a: a.id.attribute.is_position()).astype(np.int8)
        self.both_pos_mat = pd.DataFrame(np.outer(self.is_pos_vec, self.is_pos_vec), columns=index, index=index)

        self.is_h_vec = anchor_vec.map(lambda a: a.id.attribute.is_horizontal()).astype(np.int8)
        self.is_v_vec = anchor_vec.map(lambda a: a.id.attribute.is_vertical()).astype(np.int8)

        self.both_h_mat = pd.DataFrame(np.outer(self.is_h_vec, self.is_h_vec), columns=index, index=index)
        self.both_v_mat = pd.DataFrame(np.outer(self.is_v_vec, self.is_v_vec), columns=index, index=index)

        # Note: this matrix is _not_ symmetric and that's the way we want it!
        self.same_attr_mat = anchor_mat.applymap(lambda p: p[0].attribute == p[1].attribute).astype(np.int8)
        self.dual_attr_mat = anchor_mat.applymap(lambda p: Attribute.is_dual_pair(p[0].attribute, p[1].attribute)).astype(np.int8)

        self.hv_mat = pd.DataFrame(np.outer(self.is_h_vec, self.is_v_vec), columns=index, index=index)

        # 3. Encode visibility graph as adjacency matrix.
        visibilities = set(flatten(
            [(p[0].anchor.id, p[1].anchor.id) for p in visible_pairs(example, deep=True)]
            for example
            in examples
        ))
        self.visible_mat = anchor_mat.applymap(lambda p: (p[0].id, p[1].id) in visibilities).astype(np.int8)
        self.visible_mat |= self.visible_mat.transpose()

        # 4. Encode view-level facts, such as visibilities (these involve quantification over a view's anchors).
        self.same_view_mat = anchor_mat.applymap(lambda p: p[0].view == p[1].view) \
            .astype(np.int8) \
            .groupby(axis=0, level=0).any() \
            .groupby(axis=1, level=0).any()

        self.h_vis_view_mat = (self.both_h_mat & self.visible_mat) \
            .groupby(axis=0, level=0).any() \
            .groupby(axis=1, level=0).any()

        self.v_vis_view_mat = (self.both_v_mat & self.visible_mat) \
            .groupby(axis=0, level=0).any() \
            .groupby(axis=1, level=0).any()

        # 5. Encode parent/child, sibling, and same-view relationships as matrices.
        self.parent_mat = anchor_mat.applymap(lambda p: p[0].view.is_parent_of(p[1].view)).astype(np.int8)
        self.sibling_mat = anchor_mat.applymap(lambda p: p[0].view.is_sibling_of(p[1].view)).astype(np.int8)

    def instantiate(self) -> Sequence[IConstraint]:
        pd.set_option('display.width', None)
        pd.set_option('display.max_colwidth', None)
        pd.set_option('display.max_rows', None)
        pd.set_option('display.max_columns', None)

        # 1. Aspect ratios.
        aspect_ratio_mat = self.same_view_mat.mul(self.both_size_mat & self.hv_mat, level=0)

        # 2. Parent-relative size.
        parent_relative_size_mat = self.parent_mat & self.both_size_mat & (self.both_h_mat | self.both_v_mat)

        # 2. Absolute sizes.
        absolute_size_vec = self.is_size_vec

        # 3. Offset positions.
        offset_pos_pc_mat = self.parent_mat & self.both_pos_mat & self.same_attr_mat & self.visible_mat
        offset_pos_sib_mat = self.sibling_mat & self.both_pos_mat & self.dual_attr_mat & self.visible_mat
        offset_pos_mat = offset_pos_pc_mat | offset_pos_sib_mat

        # 4. Align positions.
        align_h_mat = self.v_vis_view_mat.mul(self.both_h_mat & self.sibling_mat & self.both_pos_mat & self.same_attr_mat, level=0)
        align_v_mat = self.h_vis_view_mat.mul(self.both_v_mat & self.sibling_mat & self.both_pos_mat & self.same_attr_mat, level=0)
        align_pos_mat = align_h_mat | align_v_mat

        def gen_templates():
            for pair in self.anchor_mat[aspect_ratio_mat.astype(np.bool)].stack(level=[0, 1]):
                yield ConstraintFactory.create(
                    kind=ConstraintKind.SIZE_ASPECT_RATIO,
                    y_id=pair[0].id,
                    x_id=pair[1].id,
                    op=operator.eq
                )

            for pair in self.anchor_mat[parent_relative_size_mat.astype(np.bool)].stack(level=[0, 1]):
                yield ConstraintFactory.create(
                    kind=ConstraintKind.SIZE_RATIO,
                    y_id=pair[0].id,
                    x_id=pair[1].id,
                    op=operator.eq
                )

            for pair in self.anchor_mat.iloc[:, 0][absolute_size_vec.astype(np.bool)]:
                yield ConstraintFactory.create(
                    kind=ConstraintKind.SIZE_CONSTANT,
                    y_id=pair[0].id,
                    op=operator.eq
                )

            for pair in self.anchor_mat[(offset_pos_mat | align_pos_mat).astype(np.bool)].stack(level=[0, 1]):
                yield ConstraintFactory.create(
                    kind=ConstraintKind.POS_LTRB_OFFSET,
                    y_id=pair[0].id,
                    x_id=pair[1].id,
                    op=operator.eq
                )

        return list(gen_templates())
