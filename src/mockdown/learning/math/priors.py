from itertools import tee
from statistics import mean, stdev, median
from typing import List

from sympy import Rational, N
from sympy.ntheory import continued_fraction
from sympy.sets import FiniteSet
from sympy.stats import Binomial, BetaBinomial, density, E, P, Normal
from sympy.stats.rv import sampling_E, cdf

from mockdown.learning.math.sequences import q_ball


def irrationality(q: Rational):
    """
    Note: this sum is equal to the depth in the Stern-Brocot tree.

    The "irrationality" is more properly defined as length, but this works better.
    """
    return sum(continued_fraction(q))


def rationality_dist(min_n, max_n):
    """
    A Beta-Binomial is used because we know the number
    of "trials", but we do not know the actual probability
    of "success" of each one. We set:
    - a = 1 + 0: the most likely candidate is the most rational
    - b = 1 + n

    e.g. if we have 10 candidate values,

    For intuition on why this makes sense, see:
    - https://towardsdatascience.com/beta-distribution-intuition-examples-and-derivation-cf00f4db57af
    - https://homepage.divms.uiowa.edu/~mbognar/applets/beta.html
    """
    n = max_n - min_n
    return BetaBinomial('RationalityPrior', n, 1, 1 + n)


def rationality_score_function(qs: 'FiniteSet[Rational]'):
    xs = {q: irrationality(q) for q in qs}
    min_score = min(xs.values())
    max_score = max(xs.values())

    d = rationality_dist(min_score, max_score)

    def score_function(q: Rational):
        # Note: q must be in the qs above. This distribution is not continuous!
        pass


def error_prior(mu, sigma):
    return Normal('ErrorPrior', mu, sigma)


def main():
    qs = q_ball(Rational(6/71), 0.05 * (6/71), max_denominator=100)
    scores = {q: irrationality(q) for q in qs}

    # min and max # of "trials"
    min_score = min(scores.values())
    max_score = max(scores.values())

    x = rationality_dist(min_score, max_score)
    y = error_prior(median(map(float, qs)), stdev(map(float, qs)))

    # print(density(x))
    # print(cdf(x))

    print(cdf(y))

    for q in sorted(qs):
        n_score = (scores[q] - min_score) / (max_score - min_score)
        print("rational", "depth", "1 - cdf", "pdf")
        print(q,
              scores[q],
              # f"{N(1 - cdf(y)(scores[q] - min_score)):.4f}",
              f"{N(1 - cdf(x)[scores[q] - min_score]):.4f}",
              f"{N(density(x)(scores[q] - min_score)):.4f}",
              sep='\t')

    # print(density())


if __name__ == '__main__':
    main()
