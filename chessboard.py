"""
From a friend's interview: 

    Say you're shown a chessboard with a quarter placed on each of the 64 squares. Each
    quarter is randomly Heads or Tails. You're told a square (e.g. D3), and your goal is
    to communicate that square to a friend. To do so you must flip one of the quarters.
    You then leave the room, your friend enters and looks at the quarters and finds the
    special square.

    Assume the board has an orientation: both of you know which square is A1.
"""

from collections import defaultdict
import itertools
from typing import List, NamedTuple, Optional
from hypothesis import given, strategies as st

# Here are some helpers which will make testing easier:

def random_boards(n: int) -> st.SearchStrategy:
    """Our "chessboard" is a list of booleans, True -> Heads, False -> Tails"""
    length = 2**n
    return st.lists(elements=st.booleans(), min_size=length, max_size=length)

def special_squares(n: int) -> st.SearchStrategy:
    "The square to find is an index into the board"
    length = 2**n
    return st.integers(
        min_value=0,
        max_value=length-1
    )

class Example(NamedTuple):
    n: int
    board: List[bool]
    special_square: int

@st.composite
def examples(draw, n: Optional[int] = None):
    if n is None:
        n = draw(st.integers(min_value=1, max_value=6))
    board = draw(random_boards(n))
    special_square = draw(special_squares(n))
    return Example(n, board, special_square)

# Quick sanity check:

@given(examples())
def test_hypothesis_example(ex):
    assert len(ex.board) == 2**ex.n
    assert ex.special_square >= 0
    assert ex.special_square < len(ex.board)

# Now that we've warmed up, if the board is a 2x1 this is easy:

def decide_2_by_1_board(board: List[bool]) -> int:
    "it only takes one bit to mark the special square. The other coin is a no-op"
    if board[0]:
        return 0
    return 1

def flip_2_by_1_board(special_square: int, board: List[bool]) -> int:
    """
    As the flipper:
    - If square 0 is already in the correct position, flip the no-op coin
    - Otherwise, flip square 0
    """
    if decide_2_by_1_board(board) == special_square:
        return 1
    return 0

@given(examples(1))
def test_2_by_1(ex):
    square_to_flip = flip_2_by_1_board(ex.special_square, ex.board)
    ex.board[square_to_flip] = not ex.board[square_to_flip]
    assert decide_2_by_1_board(ex.board) == ex.special_square

"""
To mark a 2x2 board we must communicate 2 bits of information
because we only have one flip, we need an encoding scheme which lets our flip:
change nothing | change the first bit | change the second bit | change both

If the chessboard has squares: 0 1
                               2 3

The first bit is whether (0, 1) are both heads or both tails (the head count is even)
  I'll use this bit to indicate that the special square is at the right
The second bit is whether (0, 2) are both heads or both tails
  I'll use this bit to indicate that the special square is at the bottom

So, in T T
       T T, both bits are true. This means the special square is 3.

    in T H
       H T, both bits are false, so the special square is 0.

To change nothing: flip 3
To change just the first bit: flip 1
To change just the second bit: flip 2
To change both: flip 0

Because we can express any combination of bit flips it's possible to start at any state
and get to a state representing any special square with just a single coin flip.
"""

def decide_2_by_2_board(board: List[bool]) -> int:
    ones_place = board[0] ^ board[1]
    twos_place = board[0] ^ board[2]
    return (2 if twos_place else 0) + (1 if ones_place else 0)

def flip(board: List[bool], square: int) -> List[bool]:
    return board[:square] + [not board[square]] + board[square+1:]

def flip_2_by_2_board(special_square: int, board: List[bool]) -> int:
    "There's a better version but this is more readable for now"
    for possible_flip in range(len(board)):
        if decide_2_by_2_board(flip(board, possible_flip)) == special_square:
            return possible_flip

    assert False

@given(examples(n=2))
def test_2_by_2(ex):
    square_to_flip = flip_2_by_2_board(ex.special_square, ex.board)
    flipped = flip(ex.board, square_to_flip)
    assert decide_2_by_2_board(flipped) == ex.special_square

# The above method for choosing your flip works because decide() has a special property
# which is necessary for satisfying the constraint that you flip a single quarter:

@given(random_boards(2))
def test_all_states_reachable(board):
    """
    - Each board position indicates a given special square
    - Starting from any board position: a single flip is sufficient to reach a board
      position indicating any special square
    """
    reachable_states = set(
        decide_2_by_2_board(flip(board, i))
        for i in range(len(board))
    )

    assert reachable_states == set(range(len(board)))

"""
The above technique generalizes to any chessboard of size 2**n. Each board state
represents some special square. There are 2**n different special squares you need to
distinguish between, so you need to somehow encode those n bits into the board state.
Because you only have one coin flip, you need to find an encoding such that every possibe
combination of bit flips (each element of the powerset of all bits) can be expressed by
one coin flip. 

The trick is that the set of every possible bit flip is exactly the integers from 2**n!

Here are all the binary numbers of size 3:
    0 - 000 - 0 bits
    1 - 001  - 1 bit
    2 - 010  - 1 bit
    3 - 011   - 2 bits
    4 - 100  - 1 bit
    5 - 101   - 2 bits
    6 - 110   - 2 bits
    7 - 111    - 3 bits

Concretely: if you have a chessboard of size 2x4 (length 8) you need three bits to encode
the position of the special square. The zeroith square has no impact on what the board
represents, this serves as a no-op in the very unlikely case that the board already
represents the square you're supposed to tell your friend. The first square contributes to
the third bit, flipping the coin on that square flips the last bit. The last square
contributes to all three bits, flipping it flips all three bits.

This makes the flipping procedure very simple: xor the square currently indicated with the
square you want to indicate then flip the coin which flips those bits you want to flip.

The decision procedure is a little more complicated: for each integer toggle the bits
which it contributes to, and finally return the square which corresponds to the sum of all
those bits.

   Alternatively: for each bit find all the integers which contribute to that bit then sum
   their contributions. That should give you the same answer.
"""

def decide_n_by_n_board(board: List[bool]) -> int:
    result = 0

    for i, coin in enumerate(board):
        if not coin:
            continue
        result ^= i

    return result

def flip_n_by_n_board(special_square: int, board: List[bool]) -> int:
    current_square = decide_n_by_n_board(board)
    bits_to_flip = current_square ^ special_square
    return bits_to_flip

@given(examples(n=6))
def test_8_by_8(ex):
    square_to_flip = flip_n_by_n_board(ex.special_square, ex.board)
    flipped = flip(ex.board, square_to_flip)
    assert decide_n_by_n_board(flipped) == ex.special_square

# That's it! Another check of the everything-is-one-flip-away condition:

@given(random_boards(6))
def test_all_states_reachable_n(board):
    reachable_states = set(
        decide_n_by_n_board(flip(board, i))
        for i in range(len(board))
    )

    assert reachable_states == set(range(len(board)))

# And just to triple check, we can write these methods in different ways and hope for the
# same answers:

def head_count_is_even(items: List[bool]) -> bool:
    # sum(List[bool]) treats True as 1, and False as 0
    return sum(items) % 2 == 0

def test_even_head_count():
    # I couldn't find a way to hypothesis this which was as pretty and succinct as just
    # hard-coding some tests
    assert head_count_is_even([])
    assert head_count_is_even([True, True])
    assert not head_count_is_even([True])
    assert not head_count_is_even([True, False, False])
    assert head_count_is_even([True, True, False])
    assert head_count_is_even([True, False, False, True])

def decide_n_by_n_board_alt(board: List[bool]) -> int:
    """
    Previously we iterated over each coin and added their contributions to bits
    Another way would be to iterate over the bits and find the coins which contribute to
      them
    """
    result = 0
    n = (len(board) - 1).bit_length()

    for bit in range(n):
        matching_indices = [
            i for i in range(len(board))
            if (i & (2**bit)) != 0
        ]
        coins = [board[i] for i in matching_indices]
        is_even = head_count_is_even(coins)

        if is_even:
            result += 2**bit

    return result

@given(examples(2))
def test_decide(ex):
    first_answer = decide_n_by_n_board(ex.board)
    second_answer = decide_n_by_n_board_alt(ex.board)

    # these two methods start counting from different ends, invert the answer here:
    length = (2**ex.n) - 1

    second_answer = length - second_answer

    assert first_answer == second_answer

def flip_n_by_n_board_cheat(special_square: int, board: List[bool]) -> int:
    "Given that the reachability tests passes this is guaranteed to work"
    for possible_flip in range(len(board)):
        if decide_n_by_n_board(flip(board, possible_flip)) == special_square:
            return possible_flip

    assert False

@given(random_boards(6), special_squares(6))
def test_flip_methods_agree(board, special_square):
    cheating_answer = flip_n_by_n_board_cheat(special_square, board)
    fancy_answer = flip_n_by_n_board(special_square, board)
    assert cheating_answer == fancy_answer
