from itertools import combinations
from collections import Counter
from pprint import pprint
from io import StringIO
import re, sys

def flat(lists):
    return sum(list(lists), [])

def mkpair(x, y):
    if x == y:
        raise ValueError("mkpair(%r, %r) - args must differ" % (x, y))
    return (y, x) if x > y else (x, y)

def triple(a, b, c):
    return [mkpair(a,b), mkpair(a,c), mkpair(b,c)]

def quad(a, b, c, d):
    return [mkpair(a, b), mkpair(a, c), mkpair(a, d),
        mkpair(b, c), mkpair(b, d), mkpair(c, d)
    ]

def allpairs(xs):
    return combinations(xs, 2)

def alltriples(xs):
    return combinations(xs, 3)

def todot(pairarr):
    return str.join('\n',
        ["graph {"] +
        ["  %s -- %s" % (a, b) for a, b in pairarr] +
        ["}"]
        )

def mercury2quads(input):
    """
    Parser of Mercury output -> list of quadruples
    Example format: [[{1, 2, 3, 4}, {5, 6, 7, 8}], [{...}, {...}]]
    """
    def peek():
        assert len(input) > 0, "unexpected end of input"
        return input[0]
    def consume1():
        nonlocal input
        input = input[1:]
    def consume_ws():
        while peek() == ' ':
            consume1()
    def parse_int():
        nonlocal input
        match = re.match(r'\d+', input)
        if not match:
            raise ValueError("int expected at %s" % input[:20])
        else:
            l = match.end()
            s, input = input[:l], input[l:]
            return int(s)
    def parse_set():
        assert peek() == '{'
        consume1()
        acc = []
        while True:
            if peek() == '}':
                consume1()
                return tuple(acc)
            if peek() == ',':
                consume1()
                consume_ws()
                continue
            acc.append(parse_int())
    def parse_list():
        assert peek() == '['
        consume1()
        acc = []
        while True:
            if peek() == ']':
                consume1()
                return acc
            if peek() == '[':
                acc.append(parse_list())
                continue
            if peek() == '{':
                acc.append(parse_set())
                continue
            if peek() == ',':
                consume1()
                consume_ws()
                continue
            raise ValueError("unexpected input in list literal: %r" % input[:20])

    return flat(parse_list())

def check_mercury_seating(str):
    pairs = flat(map(lambda s: quad(*s), mercury2quads(str)))
    isects = intersections(pairs)
    print()
    print("%d intersections in this seating:\n%s" % (len(isects), str))
    if len(isects):
        print("namely:")
        pprint(intersections(pairs))

def intersections(pairarr):
    return {p: count for p, count in Counter(pairarr).items()
        if count > 1
    }

def filterpls(pairarr, pls):
    return [p for p in pairarr if p[0] in pls and p[1] in pls]

def seating1():
    return sum([
        # H1
        quad(1, 2, 3, 26),
        quad(5, 6, 7, 8),
        quad(9, 10, 11, 12),
        quad(13, 14, 27, 16),
        quad(17, 28, 19, 20),
        quad(21, 22, 23, 24),
        # H2
        quad(1, 5, 9, 13),
        quad(2, 6, 10, 14),
        quad(3, 7, 17, 21),
        quad(26, 8, 28, 22),
        quad(11, 27, 19, 23),
        quad(12, 16, 20, 24),
        # H3
        quad(1, 6, 11, 16),
        quad(2, 5, 12, 27),
        quad(3, 8, 19, 24),
        quad(26, 7, 20, 23),
        quad(9, 14, 27, 22),
        quad(10, 13, 28, 21),
        # H4
        quad(1, 7, 10, 27),
        quad(2, 8, 9, 16),
        quad(3, 5, 28, 23),
        quad(26, 6, 17, 24),
        quad(11, 14, 20, 21),
        quad(12, 13, 19, 22),
        # H5
        quad(1, 8, 12, 14),
        quad(2, 13, 17, 23),
        quad(3, 27, 20, 22),
        quad(26, 5, 10, 16),
        quad(6, 9, 19, 21),
        quad(7, 11, 28, 24),
        # H6
        quad(1, 17, 22, 11),
        quad(2, 28, 16, 19),

        quad(3, 6, 12, 13),
        quad(8, 10, 20, 23),
        # 12-21-26

        # quad(7, 9, 24, 26), quad(5, 14, 21, 27)
        quad(7, 9, 26, 27), quad(5, 14, 21, 24)
        # 5 7 9 14 21 24 26 27
    ], [])

if __name__=="__main__":
    pls = [1,2,3,  5,6,7,8,9,10,11,12,13,14,  16,17,  19,20,21,22,23,24,  26,27, 28]

    print("seating1 has %d pairs now." % len(seating1()))
    print("%d pairs total possible" % len(list(allpairs(pls))))

    remain = set(allpairs(pls)) - set(seating1())
    remain_tris = [t
        for t in alltriples(pls)
        if remain.issuperset(triple(*t))
        ]

    print("remaining triples:")
    pprint(remain_tris)
    with open("seating.dot", 'w') as gv:
        print(todot(remain), file=gv)
        # print(todot(filterpls(remain, [5,7,9,14,21,24,26,27])), file=gv)
        # print(todot(set(flat(map(lambda t: triple(*t), remain_tris)))), file=gv)

    print("seating1 intersections:")
    pprint(intersections(seating1()))

    #-- egrep '^[[]' data/seatings.P24.H6.dump | python intersections.py
    for s in sys.stdin:
        check_mercury_seating(s)
