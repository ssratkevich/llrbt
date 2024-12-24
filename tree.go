/*
	Package llrbt is a golang implementation of Left-leaning Red-Black Trees

Based on works of Robert Sedgewick:
- https://sedgewick.io/wp-content/themes/sedgewick/papers/2008LLRB.pdf
- https://sedgewick.io/wp-content/uploads/2022/03/2008-09LLRB.pdf
- https://algs4.cs.princeton.edu/33balanced/RedBlackBST.java.html
*/
package llrbt

import "iter"

// Comparable interface allows to key comparison
//
// -1 a < b
// 0 a == b
// 1 a > b
//type func Compare[T any](a, b T) int

type node[Key any, Value any] struct {
	key         Key
	value       Value
	left, right *node[Key, Value]
	red         bool
	size        int
}

func newNode[Key any, Value any](key Key, val Value, red bool, size int) *node[Key, Value] {
	return &node[Key, Value]{
		key:   key,
		value: val,
		red:   red,
		size:  size,
	}
}

// Tree is a left-leaning Red-Black Tree.
//
// It's an ordered tree, witch order dictated by comparison function for its keys.
//
// Important!
//
// No key mutations is detected by the tree. Don't modify keys after they are inserted in the tree.
type Tree[Key any, Value any] struct {
	root *node[Key, Value]
	comp func(a, b Key) int
}

// NewTree creates new instance of Left-leaning red-black tree with a given comparison function for it's keys.
//
// comp - key comparison function. Gives a freedom to compare keys in user supplied manner.
// For instance, compare pointers by their values.
func NewTree[Key any, Value any](comp func(a, b Key) int) *Tree[Key, Value] {
	if comp == nil {
		panic("key comparator must be provided")
	}
	return &Tree[Key, Value]{
		comp: comp,
	}
}

// Size - returns the number of key-value pairs in the tree.
func (t *Tree[Key, Value]) Size() int {
	return size(t.root)
}

// Empty - check wither tree is empty.
func (t *Tree[Key, Value]) Empty() bool {
	return t.root == nil
}

// Get - returns the value associated with the given key, and ok flag that a value successively found.
func (t *Tree[Key, Value]) Get(key Key) (value Value, ok bool) {
	return t.get(t.root, key)
}

func (t *Tree[Key, Value]) get(node *node[Key, Value], key Key) (value Value, ok bool) {
	x := node
	for x != nil {
		cmp := t.comp(key, x.key)
		if cmp < 0 {
			x = x.left
		} else if cmp > 0 {
			x = x.right
		} else {
			return x.value, true
		}
	}
	return
}

// Set - add or update value by its key in the tree.
func (t *Tree[Key, Value]) Set(key Key, value Value) {
	t.root = t.set(t.root, key, value)
	t.root.red = false
}

func (t *Tree[Key, Value]) set(h *node[Key, Value], key Key, val Value) *node[Key, Value] {
	if h == nil {
		return newNode(key, val, true, 1)
	}
	cmp := t.comp(key, h.key)
	if cmp < 0 {
		h.left = t.set(h.left, key, val)
	} else if cmp > 0 {
		h.right = t.set(h.right, key, val)
	} else {
		h.value = val
	}

	// fix-up any right-leaning links
	if isRed(h.right) && !isRed(h.left) {
		h = rotateLeft(h)
	}
	if isRed(h.left) && isRed(h.left.left) {
		h = rotateRight(h)
	}
	if isRed(h.left) && isRed(h.right) {
		flipColors(h)
	}
	h.size = size(h.left) + size(h.right) + 1

	return h
}

// DeleteMin - removes the smallest key and associated value from the tree.
func (t *Tree[Key, Value]) DeleteMin() {
	if t.Empty() {
		return
	}

	// if both children of root are black, set root to red
	if !isRed(t.root.left) && !isRed(t.root.right) {
		t.root.red = true
	}

	t.root = deleteMin(t.root)
	if !t.Empty() {
		t.root.red = false
	}
}

// DeleteMax - removes the largest key and associated value from the symbol table.
func (t *Tree[Key, Value]) DeleteMax() {
	if t.Empty() {
		return
	}

	// if both children of root are black, set root to red
	if !isRed(t.root.left) && !isRed(t.root.right) {
		t.root.red = true
	}

	t.root = deleteMax(t.root)
	if !t.Empty() {
		t.root.red = false
	}
}

// Delete - removes the specified key and its associated value from the tree.
func (t *Tree[Key, Value]) Delete(key Key) {
	if _, ok := t.get(t.root, key); !ok {
		return
	}

	// if both children of root are black, set root to red
	if !isRed(t.root.left) && !isRed(t.root.right) {
		t.root.red = true
	}

	t.root = delete(t.root, key, t.comp)
	if !t.Empty() {
		t.root.red = false
	}
}

// Clean - flushes the tree.
func (t *Tree[Key, Value]) Clean() {
	// simply set root to nil
	// but in advanced scenario
	// need to free every node without tree rotation
	t.root = nil
}

// GetAll - provides key-value iterator.
func (t *Tree[Key, Value]) GetAll() iter.Seq2[Key, Value] {
	return func(yield func(Key, Value) bool) {
		walk(t.root, yield)
	}
}

func walk[Key any, Value any](x *node[Key, Value], fn func(Key, Value) bool) {
	if x == nil {
		return
	}
	walk(x.left, fn)
	if !fn(x.key, x.value) {
		return
	}
	walk(x.right, fn)
}

// Height - returns the height of the tree.
func (t *Tree[Key, Value]) Height() int {
	return height(t.root)
}

// Min - returns the smallest key in the tree.
func (t *Tree[Key, Value]) Min() (key Key, ok bool) {
	if t.Empty() {
		return
	}
	n := min(t.root)
	return n.key, ok
}

// Max - returns the largest key in the tree.
func (t *Tree[Key, Value]) Max() (key Key, ok bool) {
	if t.Empty() {
		return
	}
	n := max(t.root)
	return n.key, ok
}

// Floor - returns the largest key in the tree less than or equal to given key.
func (t *Tree[Key, Value]) Floor(key Key) (k Key, ok bool) {
	if t.Empty() {
		return
	}
	x := floor(t.root, key, t.comp)
	if x == nil {
		return
	}
	return x.key, true
}

func floor[Key any, Value any](x *node[Key, Value], key Key, comp func(a, b Key) int) *node[Key, Value] {
	if x == nil {
		return nil
	}
	cmp := comp(key, x.key)
	if cmp == 0 {
		return x
	}
	if cmp < 0 {
		return floor(x.left, key, comp)
	}
	if t := floor(x.right, key, comp); t != nil {
		return t
	}
	return x
}

// Ceiling - returns the largest key in the tree greater than or equal to given key.
func (t *Tree[Key, Value]) Ceiling(key Key) (k Key, ok bool) {
	if t.Empty() {
		return
	}
	x := ceiling(t.root, key, t.comp)
	if x == nil {
		return
	}
	return x.key, true
}

func ceiling[Key any, Value any](x *node[Key, Value], key Key, comp func(a, b Key) int) *node[Key, Value] {
	if x == nil {
		return nil
	}
	cmp := comp(key, x.key)
	if cmp == 0 {
		return x
	}
	if cmp > 0 {
		return ceiling(x.right, key, comp)
	}
	if t := ceiling(x.left, key, comp); t != nil {
		return t
	}
	return x
}

// Select - return the key in the tree of a given rank (i.e. index).
// This key has the property that there are rank keys in
// the tree that are smaller. In other words, this key is the
// (rank+1)st smallest key in the tree.
func (t *Tree[Key, Value]) Select(rank int) (key Key, ok bool) {
	if rank < 0 || rank > size(t.root) {
		return
	}
	return selectNode(t.root, rank)
}

func selectNode[Key any, Value any](x *node[Key, Value], rank int) (key Key, ok bool) {
	if x == nil {
		return
	}
	leftSize := size(x.left)
	if leftSize > rank {
		return selectNode(x.left, rank)
	} else if leftSize < rank {
		return selectNode(x.right, rank-leftSize-1)
	} else {
		return x.key, true
	}
}

// Rank - return the number of keys in the tree strictly less than key.
func (t *Tree[Key, Value]) Rank(key Key) int {
	return rank(key, t.root, t.comp)
}

// number of keys less than key in the subtree rooted at x
func rank[Key any, Value any](key Key, x *node[Key, Value], comp func(a, b Key) int) int {
	if x == nil {
		return 0
	}
	cmp := comp(key, x.key)
	if cmp < 0 {
		return rank(key, x.left, comp)
	} else if cmp > 0 {
		return 1 + size(x.left) + rank(key, x.right, comp)
	} else {
		return size(x.left)
	}
}

// Keys - return all keys in the tree.
func (t *Tree[Key, Value]) Keys() []Key {
	if t.Empty() {
		return nil
	}
	keyArr := make([]Key, 0, size(t.root))
	keys(t.root, min(t.root).key, max(t.root).key, t.comp, &keyArr)
	return keyArr
}

// KeysInRange - return all keys in given range [lo;hi] in the tree.
func (t *Tree[Key, Value]) KeysInRange(lo, hi Key) []Key {
	if t.Empty() {
		return nil
	}
	keyArr := []Key{}
	keys(t.root, lo, hi, t.comp, &keyArr)
	return keyArr
}

// Check - check the tree validity.
func (t *Tree[Key, Value]) Check() bool {
	if t.Empty() {
		return true
	}
	return isBST(t.root, nil, nil, t.comp) &&
		isSizeConsistent(t.root) &&
		isRankConsistent(t.root, t.comp) &&
		is23(t.root, t.root) &&
		isBalanced(t.root)
}

func isBST[Key any, Value any](x *node[Key, Value], min, max *Key, comp func(a, b Key) int) bool {
	if x == nil {
		return true
	}
	if min != nil && comp(x.key, *min) <= 0 {
		return false
	}
	if max != nil && comp(x.key, *max) >= 0 {
		return false
	}
	return isBST(x.left, min, &x.key, comp) && isBST(x.right, &x.key, max, comp)
}

func isSizeConsistent[Key, Value any](x *node[Key, Value]) bool {
	if x == nil {
		return true
	}
	if x.size != size(x.left)+size(x.right)+1 {
		return false
	}
	return isSizeConsistent(x.left) && isSizeConsistent(x.right)
}

func isRankConsistent[Key any, Value any](x *node[Key, Value], comp func(a, b Key) int) bool {
	n := size(x)
	if n == 0 {
		return true
	}

	for i := 0; i < n; i++ {
		key, ok := selectNode(x, i)
		if !ok {
			return false
		}
		if i != rank(key, x, comp) {
			return false
		}
	}

	keysArr := make([]Key, 0, n)
	keys(x, min(x).key, max(x).key, comp, &keysArr)
	for _, key := range keysArr {
		selKey, ok := selectNode(x, rank(key, x, comp))
		if !ok {
			return false
		}
		if comp(key, selKey) != 0 {
			return false
		}
	}
	return true
}

func is23[Key any, Value any](root, x *node[Key, Value]) bool {
	if x == nil {
		return true
	}
	if isRed(x.right) {
		return false
	}
	if x != root && isRed(x) && isRed(x.left) {
		return false
	}
	return is23(root, x.left) && is23(root, x.right)
}

func isBalanced[Key any, Value any](h *node[Key, Value]) bool {
	black := 0
	x := h
	for x != nil {
		if !isRed(x) {
			black++
		}
		x = x.left
	}
	return isBalanced2(h, black)
}

func isBalanced2[Key any, Value any](x *node[Key, Value], black int) bool {
	if x == nil {
		return black == 0
	}
	if !isRed(x) {
		black--
	}
	return isBalanced2(x.left, black) && isBalanced2(x.right, black)
}

func keys[Key any, Value any](x *node[Key, Value], lo, hi Key, comp func(a, b Key) int, arr *[]Key) {
	if x == nil {
		return
	}
	cmplo := comp(lo, x.key)
	cmphi := comp(hi, x.key)
	if cmplo < 0 {
		keys(x.left, lo, hi, comp, arr)
	}
	if cmplo <= 0 && cmphi >= 0 {
		*arr = append(*arr, x.key)
	}
	if cmphi > 0 {
		keys(x.right, lo, hi, comp, arr)
	}
}

// delete the key-value pair with the minimum key rooted at h
func deleteMin[Key any, Value any](h *node[Key, Value]) *node[Key, Value] {
	if h.left == nil {
		return nil
	}

	if !isRed(h.left) && !isRed(h.left.left) {
		h = moveRedLeft(h)
	}

	h.left = deleteMin(h.left)
	return balance(h)
}

// delete the key-value pair with the maximum key rooted at h
func deleteMax[Key any, Value any](h *node[Key, Value]) *node[Key, Value] {
	if isRed(h.left) {
		h = rotateRight(h)
	}

	if h.right == nil {
		return nil
	}

	if !isRed(h.right) && !isRed(h.right.left) {
		h = moveRedRight(h)
	}

	h.right = deleteMax(h.right)
	return balance(h)
}

func delete[Key any, Value any](h *node[Key, Value], key Key, comp func(a, b Key) int) *node[Key, Value] {
	if comp(key, h.key) < 0 {
		if !isRed(h.left) && !isRed(h.left.left) {
			h = moveRedLeft(h)
		}
		h.left = delete(h.left, key, comp)
	} else {
		if isRed(h.left) {
			h = rotateRight(h)
		}
		if comp(key, h.key) == 0 && h.right == nil {
			return nil
		}
		if !isRed(h.right) && !isRed(h.right.left) {
			h = moveRedRight(h)
		}
		if comp(key, h.key) == 0 {
			x := min(h.right)
			h.key = x.key
			h.value = x.value
			h.right = deleteMin(h.right)
		} else {
			h.right = delete(h.right, key, comp)
		}
	}
	return balance(h)
}

func height[Key any, Value any](x *node[Key, Value]) int {
	if x == nil {
		return -1
	}
	lh := height(x.left)
	rh := height(x.right)
	if lh < rh {
		lh = rh
	}
	return lh + 1
}

// make a left-leaning link lean to the right
func rotateRight[Key any, Value any](h *node[Key, Value]) *node[Key, Value] {
	if h == nil || !isRed(h.left) {
		panic("wrong right rotate")
	}
	x := h.left
	h.left = x.right
	x.right = h
	x.red = h.red
	h.red = true
	x.size = h.size
	h.size = size(h.left) + size(h.right) + 1
	return x
}

// make a right-leaning link lean to the left
func rotateLeft[Key any, Value any](h *node[Key, Value]) *node[Key, Value] {
	if h == nil || !isRed(h.right) {
		panic("wrong left rotate")
	}
	x := h.right
	h.right = x.left
	x.left = h
	x.red = h.red
	h.red = true
	x.size = h.size
	h.size = size(h.left) + size(h.right) + 1
	return x
}

// flip the colors of a node and its two children
func flipColors[Key any, Value any](h *node[Key, Value]) {
	h.red = !h.red
	h.left.red = !h.left.red
	h.right.red = !h.right.red
}

// Assuming that h is red and both h.left and h.left.left
// are black, make h.left or one of its children red.
func moveRedLeft[Key any, Value any](h *node[Key, Value]) *node[Key, Value] {
	flipColors(h)
	if isRed(h.right.left) {
		h.right = rotateRight(h.right)
		h = rotateLeft(h)
		flipColors(h)
	}
	return h
}

// Assuming that h is red and both h.right and h.right.left
// are black, make h.right or one of its children red.
func moveRedRight[Key any, Value any](h *node[Key, Value]) *node[Key, Value] {
	flipColors(h)
	if isRed(h.left.left) {
		h = rotateRight(h)
		flipColors(h)
	}
	return h
}

// restore red-black tree invariant
func balance[Key any, Value any](h *node[Key, Value]) *node[Key, Value] {
	if isRed(h.right) && !isRed(h.left) {
		h = rotateLeft(h)
	}
	if isRed(h.left) && isRed(h.left.left) {
		h = rotateRight(h)
	}
	if isRed(h.left) && isRed(h.right) {
		flipColors(h)
	}

	h.size = size(h.left) + size(h.right) + 1
	return h
}

func min[Key any, Value any](x *node[Key, Value]) *node[Key, Value] {
	if x.left == nil {
		return x
	}
	return min(x.left)
}

func max[Key any, Value any](x *node[Key, Value]) *node[Key, Value] {
	if x.right == nil {
		return x
	}
	return max(x.right)
}

func isRed[Key any, Value any](node *node[Key, Value]) bool {
	return node != nil && node.red
}

func size[Key any, Value any](node *node[Key, Value]) int {
	if node == nil {
		return 0
	}
	return node.size
}
