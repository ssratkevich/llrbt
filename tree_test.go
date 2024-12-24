package llrbt

import (
	"slices"
	"strconv"
	"testing"

	"github.com/stretchr/testify/require"
)

type pair[Key any, Value any] struct {
	key Key
	val Value
}

func TestSimple(t *testing.T) {

	arr := []pair[int, string]{
		{10, "a"},
		{-1, "b"},
		{3, "c"},
		{-5, "d"},
		{5, "e"},
		{-10, "f"},
	}
	tree := NewTree[int, string](func(a, b int) int { return a - b })
	for _, c := range arr {
		tree.Set(c.key, c.val)
	}
	slices.SortFunc(arr, func(a, b pair[int, string]) int { return a.key - b.key })
	require.True(t, tree.Check())
	require.Equal(t, len(arr), tree.Size())
	keys := tree.Keys()
	require.Equal(t, len(keys), len(arr))
	for i, k := range keys {
		require.Equal(t, k, arr[i].key)
		val, ok := tree.Get(k)
		require.True(t, ok)
		require.Equal(t, val, arr[i].val)
	}
}

func TestArr(t *testing.T) {
	t.Run("test 10", func(t *testing.T) {
		testN(t, 10, false)
	})
	t.Run("test 10 rev", func(t *testing.T) {
		testN(t, 10, true)
	})
	t.Run("test 100", func(t *testing.T) {
		testN(t, 100, false)
	})
	t.Run("test 100 rev", func(t *testing.T) {
		testN(t, 100, true)
	})
	t.Run("test 1000", func(t *testing.T) {
		testN(t, 1000, false)
	})
	t.Run("test 1000 rev", func(t *testing.T) {
		testN(t, 1000, true)
	})
	t.Run("test 10 000", func(t *testing.T) {
		testN(t, 10_000, false)
	})
	t.Run("test 10 000 rev", func(t *testing.T) {
		testN(t, 10_000, true)
	})
	t.Run("test 100 000", func(t *testing.T) {
		testN(t, 100_000, false)
	})
	t.Run("test 100 000 rev", func(t *testing.T) {
		testN(t, 100_000, true)
	})
	t.Run("test 1 000 000", func(t *testing.T) {
		testN(t, 1_000_000, false)
	})
	t.Run("test 1 000 000 rev", func(t *testing.T) {
		testN(t, 1_000_000, true)
	})
}

func testN(t *testing.T, n int, rev bool) {
	tree := NewTree[int, struct{}](func(a, b int) int { return a - b })
	if rev {
		for i := n - 1; i >= 0; i-- {
			tree.Set(i, struct{}{})
		}
	} else {
		for i := 0; i < n; i++ {
			tree.Set(i, struct{}{})
		}
	}
	require.True(t, tree.Check())
	require.Equal(t, n, tree.Size())
	for i := 0; i < n; i++ {
		_, ok := tree.Get(i)
		require.True(t, ok)
	}
}

func TestIter(t *testing.T) {
	tree := NewTree[int, string](func(a, b int) int { return a - b })
	n := 100000

	for i := 0; i < n; i++ {
		tree.Set(i, strconv.Itoa(i))
	}

	require.True(t, tree.Check())
	require.Equal(t, n, tree.Size())
	for k, v := range tree.GetAll() {
		require.GreaterOrEqual(t, k, 0)
		require.Less(t, k, n)
		require.Equal(t, strconv.Itoa(k), v)
	}
}

func TestDelete(t *testing.T) {
	tree := NewTree[int, string](func(a, b int) int { return a - b })
	n := 100000

	for i := 0; i < n; i++ {
		tree.Set(i, strconv.Itoa(i))
	}

	require.True(t, tree.Check())
	require.Equal(t, n, tree.Size())

	for i := n - 1; i >= 0; i-- {
		tree.Delete(i)
		_, ok := tree.Get(i)
		require.False(t, ok)
		require.Equal(t, i, tree.Size())
	}

	require.True(t, tree.Check())
	require.Equal(t, 0, tree.Size())
}

func TestDeleteMin(t *testing.T) {
	tree := NewTree[*int, string](func(a, b *int) int {
		if a != nil && b != nil {
			return *a - *b
		}
		if a == nil && b == nil {
			return 0
		}
		if a != nil {
			return 1
		}
		return -1
	})
	n := 100000

	for i := 0; i < n; i++ {
		j := i
		tree.Set(&j, strconv.Itoa(i))
	}

	require.True(t, tree.Check())
	require.Equal(t, n, tree.Size())

	for i := 0; i < n; i++ {
		j := i
		tree.DeleteMin()
		_, ok := tree.Get(&j)
		require.False(t, ok)
		require.Equal(t, n-i-1, tree.Size())
	}

	require.True(t, tree.Check())
	require.Equal(t, 0, tree.Size())
}

func TestDeleteMax(t *testing.T) {
	tree := NewTree[*int, string](func(a, b *int) int {
		if a != nil && b != nil {
			return *b - *a
		}
		if a == nil && b == nil {
			return 0
		}
		if a != nil {
			return -1
		}
		return 1
	})
	n := 100000

	for i := 0; i < n; i++ {
		j := i
		tree.Set(&j, strconv.Itoa(i))
	}

	require.True(t, tree.Check())
	require.Equal(t, n, tree.Size())

	for i := 0; i < n; i++ {
		j := i
		tree.DeleteMax()
		_, ok := tree.Get(&j)
		require.False(t, ok)
		require.Equal(t, n-i-1, tree.Size())
	}

	require.True(t, tree.Check())
	require.Equal(t, 0, tree.Size())
}
