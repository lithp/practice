#!/usr/bin/env python3

class MinHeap:
    'A tree where the parent of a node is always smaller than the node'

    def __init__(self):
        self.items = []

    @staticmethod
    def parent(index):
        # the math is easy with 1-indexing. so convert to 1-indexing then convert the
        # answer back
        index += 1
        if index == 1:
            return None
        return (index // 2) - 1

    @staticmethod
    def children(index):
        return ((index * 2) + 1, (index * 2) + 2)

    def _swap(self, left, right):
        self.items[left], self.items[right] = self.items[right], self.items[left]

    def add(self, item):
        '''
        Add the element to the end of the array. Swap it with its parent until said
        parent is smaller than it
        '''
        self.items.append(item)
        index = len(self.items) - 1

        def parent():
            return MinHeap.parent(index)

        while index != 0 and self.items[parent()] > self.items[index]:
            self._swap(parent(), index)
            index = parent()

    def pop(self):
        '''
        Swap the element at the root of the array with the element at the end. Then push
        that element down until it's larger than it's parent.
        '''
        self._swap(0, len(self)-1)
        result = self.items.pop()

        if len(self.items) == 0:
            # there's nothing to push down!
            return result

        # now push the item down, replace it with the smallest of its children
        current_index = 0
        while True:
            children = MinHeap.children(current_index)
            indicies = [current_index, children[0], children[1]]
            without_out_of_bounds = [idx for idx in indicies if idx < len(self.items)]
            values = [(idx, self.items[idx]) for idx in without_out_of_bounds]
            smallest = min(values, key=lambda tup: tup[1])
            idx_of_smallest, _ = smallest

            if idx_of_smallest == current_index:
                # we're either a leaf node or we're smaller than our children
                break

            self._swap(current_index, idx_of_smallest)
            current_index = idx_of_smallest

        return result

    def __len__(self):
        return len(self.items)

# some tests to make sure the indexes are being correctly computed

derived_parents = [MinHeap.parent(index) for index in range(10)]
assert derived_parents == [None, 0, 0, 1, 1, 2, 2, 3, 3, 4], derived_parents

derived_children = [MinHeap.children(index) for index in range(4)]
assert derived_children == [(1, 2), (3, 4), (5, 6), (7, 8)], derived_children

for index in range(10):
    children = MinHeap.children(index)
    for child in children:
        assert MinHeap.parent(child) == index

def heapsort(items):
    '''
    given an array of items, sorts them by adding them to a min-heap and then reading off
    the smallest element until there are no more elements
    '''
    heap = MinHeap()
    [heap.add(item) for item in items]
    result = list()
    while len(heap):
        result.append(heap.pop())
    return result

if __name__ == '__main__':
    def dotest(testcase, expected):
        result = heapsort(testcase)
        if result != expected:
            print('failed. testcase: {} expected: {} result: {}'.format(
                testcase, expected, result)
            )
            exit()

    dotest([4, 3, 2, 1], [1, 2, 3, 4])
    dotest([4, 3, 2, 1, 10, 7, 4, -4], [-4, 1, 2, 3, 4, 4, 7, 10])
