use std::borrow::Borrow;
use std::ops::Index;
use std::fmt::Debug;
use std::mem;
use std::fmt;
use std::slice;
use std::vec;

#[derive(Clone)]
pub struct VecMap<K, V> {
    values: Vec<V>,
    keys: Vec<K>,
}

impl<K: Eq, V> VecMap<K, V> {
    /// Create an empty `VecMap`
    pub fn new() -> VecMap<K, V> {
        VecMap {
            values: Vec::new(),
            keys: Vec::new(),
        }
    }

    /// Create an empty `VecMap` with the given initial capacity
    pub fn with_capacity(capacity: usize) -> VecMap<K, V> {
        VecMap {
            values: Vec::with_capacity(capacity),
            keys: Vec::with_capacity(capacity),
        }
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// # Examples
    /// ```
    /// use vecmap::VecMap;
    /// let map: VecMap<isize, isize> = VecMap::with_capacity(100);
    /// assert!(map.capacity() >= 100);
    /// ```
    pub fn capacity(&self) -> usize {
        self.values.capacity()
    }

    /// Reserves capacity for at least additional more elements to be inserted
    /// in the `VecMap`. The collection may reserve more space to avoid frequent
    /// reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows usize.
    ///
    /// # Examples
    /// ```
    /// use vecmap::VecMap;
    /// let mut map: VecMap<&str, isize> = VecMap::new();
    /// map.reserve(10);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.values.reserve(additional);
    }

    /// Shrinks the capacity of the map as much as possible.
    ///
    /// # Examples
    /// ```
    /// use vecmap::VecMap;
    /// let mut map: VecMap<isize, isize> = VecMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() == 2);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.values.shrink_to_fit();
    }

    /// An iterator visiting all keys in insertion order.
    /// Iterator element type is `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// for key in map.keys() {
    ///     println!("{}", key);
    /// }
    /// ```
    pub fn keys(&self) -> Keys<K> {
        Keys{inner: self.keys.iter()}
    }

    /// An iterator visiting all values in insertion order.
    /// Iterator element type is `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// for val in map.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    pub fn values(&self) -> Values<V> {
        Values{inner: self.values.iter()}
    }

    /// An iterator visiting all values mutably in insertion order.
    /// Iterator element type is `&'a mut V`.
    ///
    /// # Examples
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    ///
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// for val in map.values_mut() {
    ///     *val = *val + 10;
    /// }
    ///
    /// for val in map.values() {
    ///     print!("{}", val);
    /// }
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<V> {
        ValuesMut{inner: self.values.iter_mut()}
    }

    /// An iterator visiting all key-value pairs in insertion order.
    /// Iterator element type is `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// for (key, val) in map.iter() {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            keys: self.keys.iter(),
            values: self.values.iter()
        }
    }

    /// An iterator visiting all key-value pairs in insertion order, with
    /// mutable references to the values.
    /// Iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    /// map.insert("c", 3);
    ///
    /// // Update all values
    /// for (_, val) in map.iter_mut() {
    ///     *val *= 2;
    /// }
    ///
    /// for (key, val) in &map {
    ///     println!("key: {} val: {}", key, val);
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut {
            keys: self.keys.iter(),
            values: self.values.iter_mut()
        }
    }

    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut letters = VecMap::new();
    ///
    /// for ch in "a short treatise on fungi".chars() {
    ///     let counter = letters.entry(ch).or_insert(0);
    ///     *counter += 1;
    /// }
    ///
    /// assert_eq!(letters[&'s'], 2);
    /// assert_eq!(letters[&'t'], 3);
    /// assert_eq!(letters[&'u'], 1);
    /// assert_eq!(letters.get(&'y'), None);
    /// ```
    pub fn entry(&mut self, key: K) -> Entry<K, V> {
        match self.key_index(&key) {
            Some(i) => Entry::Occupied(OccupiedEntry{
                key: &self.keys[i],
                value: &mut self.values[i]
            }),
            None => Entry::Vacant(VacantEntry{
                key: key,
                map: self
            })
        }
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut a = VecMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a");
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        debug_assert!(self.keys.len() == self.values.len());
        self.values.len()
    }

    /// Returns true if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut a = VecMap::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a");
    /// assert!(!a.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// Clears the map, returning all key-value pairs as an iterator. Keeps the
    /// allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut a = VecMap::new();
    /// a.insert(1, "a");
    /// a.insert(2, "b");
    ///
    /// for (k, v) in a.drain().take(1) {
    ///     assert!(k == 1 || k == 2);
    ///     assert!(v == "a" || v == "b");
    /// }
    ///
    /// assert!(a.is_empty());
    /// ```
    #[inline]
    pub fn drain(&mut self) -> Drain<K, V> {
        Drain {
            keys: self.keys.drain(..),
            values: self.values.drain(..),
        }
    }

    /// Clears the map, removing all key-value pairs. Keeps the allocated memory
    /// for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut a = VecMap::new();
    /// a.insert(1, "a");
    /// a.clear();
    /// assert!(a.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        self.values.clear();
        self.keys.clear();
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Eq` on the
    /// borrowed form *must* match the one for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V> where K: Borrow<Q>, Q: Eq {
        self.key_index(key).map(|i| &self.values[i])
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Eq` on the
    /// borrowed form *must* match the one for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// if let Some(x) = map.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map[&1], "b");
    /// ```
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V> where K: Borrow<Q>, Q: Eq {
        match self.key_index(key) {
            Some(i) => Some(&mut self.values[i]),
            None => None
        }
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but `Eq` on the
    /// borrowed form *must* match the one for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool where K: Borrow<Q>, Q: Eq {
        self.key_index(key).is_some()
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though; this matters for
    /// types that can be `==` without being identical.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map[&37], "c");
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.key_index(&key) {
            Some(i) => {
                let mut value = value;
                mem::swap(&mut self.values[i], &mut value);
                return Some(value);
            }
            None => {
                self.values.push(value);
                self.keys.push(key);
                return None;
            }
        }
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but `Eq` on the
    /// borrowed form *must* match the one for the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use vecmap::VecMap;
    ///
    /// let mut map = VecMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V> where K: Borrow<Q>, Q: Eq {
        match self.key_index(key) {
            Some(i) => {
                self.keys.remove(i);
                Some(self.values.remove(i))
            }
            None => None
        }
    }

    /// Find the given key in the map, and return the corresponding index, or
    /// `None`.
    fn key_index<Q: ?Sized>(&self, key: &Q) -> Option<usize> where K: Borrow<Q>, Q: Eq {
        for (i, entry) in self.keys.iter().enumerate() {
            if entry.borrow() == key {
                return Some(i);
            }
        }
        return None;
    }
}

impl<K: Eq, V> Default for VecMap<K, V> {
    fn default() -> VecMap<K, V> {
        VecMap::new()
    }
}

impl<'a, K: Eq, Q: ?Sized, V> Index<&'a Q> for VecMap<K, V> where K: Borrow<Q>, Q: Eq {
    type Output = V;

    #[inline]
    fn index(&self, index: &Q) -> &V {
        self.get(index).expect("no entry found for key")
    }
}

impl<K: Eq, V> Debug for VecMap<K, V> where K: Debug, V: Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        try!(write!(f, "{{"));
        for (k, v) in self {
            try!(write!(f, "{:?}: {:?}", k, v));
        }
        try!(write!(f, "}}"));
        Ok(())
    }
}

impl<K: Eq, V> PartialEq for VecMap<K, V> where V: PartialEq {
    fn eq(&self, other: &VecMap<K, V>) -> bool {
        unimplemented!()
    }
}

impl<K: Eq, V> Eq for VecMap<K, V> where V: Eq {}


impl<K: Eq, V> IntoIterator for VecMap<K, V> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;
    fn into_iter(self) -> IntoIter<K, V> {
        IntoIter {
            keys: self.keys.into_iter(),
            values: self.values.into_iter()
        }
    }
}

impl<'a, K: Eq, V> IntoIterator for &'a VecMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Iter<'a, K, V> {
        self.iter()
    }
}

impl<'a, K: Eq, V> IntoIterator for &'a mut VecMap<K, V> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;
    fn into_iter(self) -> IterMut<'a, K, V> {
        self.iter_mut()
    }
}

pub enum Entry<'a, K: 'a, V: 'a> where K: Eq {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

pub struct OccupiedEntry<'a, K: 'a, V: 'a> {
    key: &'a K,
    value: &'a mut V
}

pub struct VacantEntry<'a, K: 'a, V: 'a> {
    key: K,
    map: &'a mut VecMap<K, V>
}

impl<'a, K: Eq, V> Entry<'a, K, V> {
    /// Ensures a value is in the entry by inserting the default if empty, and
    /// returns a mutable reference to the value in the entry.
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.value,
            Entry::Vacant(entry) => {
                entry.map.insert(entry.key, default);
                let i = entry.map.len() - 1;
                &mut entry.map.values[i]
            },
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default
    /// function if empty, and returns a mutable reference to the value in the
    /// entry.
    pub fn or_insert_with<F>(self, default: F) -> &'a mut V where F: FnOnce() -> V {
        match self {
            Entry::Occupied(entry) => entry.value,
            Entry::Vacant(entry) => {
                entry.map.insert(entry.key, default());
                let i = entry.map.len() - 1;
                &mut entry.map.values[i]
            },
        }
    }

    /// Returns a reference to this entry's key
    pub fn key(&self) -> &K {
        match *self {
            Entry::Occupied(ref entry) => entry.key,
            Entry::Vacant(ref entry) => &entry.key,
        }
    }
}

pub struct Keys<'a, K: 'a> {
    inner: slice::Iter<'a, K>
}

impl<'a, K> Iterator for Keys<'a, K> {
    type Item = &'a K;
    fn next(&mut self) -> Option<&'a K> {
        self.inner.next()
    }
}

pub struct Values<'a, V: 'a> {
    inner: slice::Iter<'a, V>
}

impl<'a, V> Iterator for Values<'a, V> {
    type Item = &'a V;
    fn next(&mut self) -> Option<&'a V> {
        self.inner.next()
    }
}

pub struct ValuesMut<'a, V: 'a> {
    inner: slice::IterMut<'a, V>
}

impl<'a, V> Iterator for ValuesMut<'a, V> {
    type Item = &'a mut V;
    fn next(&mut self) -> Option<&'a mut V> {
        self.inner.next()
    }
}

pub struct Iter<'a, K: 'a , V: 'a > {
    keys: slice::Iter<'a, K>,
    values: slice::Iter<'a, V>
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        match self.keys.next() {
            Some(key) => {
                let value = self.values.next().expect("Internal error: invalid size for values iterator");
                Some((key, value))
            }
            None => {
                debug_assert!(self.values.next().is_none());
                None
            }
        }
    }
}

pub struct IterMut<'a, K: 'a , V: 'a > {
    keys: slice::Iter<'a, K>,
    values: slice::IterMut<'a, V>
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        match self.keys.next() {
            Some(key) => {
                let value = self.values.next().expect("Internal error: invalid size for values iterator");
                Some((key, value))
            }
            None => {
                debug_assert!(self.values.next().is_none());
                None
            }
        }
    }
}

pub struct Drain<'a, K: 'a, V: 'a> {
    keys: vec::Drain<'a, K>,
    values: vec::Drain<'a, V>
}

impl<'a, K, V> Iterator for Drain<'a, K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<(K, V)> {
        match self.keys.next() {
            Some(key) => {
                let value = self.values.next().expect("Internal error: invalid size for values iterator");
                Some((key, value))
            }
            None => {
                debug_assert!(self.values.next().is_none());
                None
            }
        }
    }
}

pub struct IntoIter<K, V> {
    keys: vec::IntoIter< K>,
    values: vec::IntoIter<V>
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<(K, V)> {
        match self.keys.next() {
            Some(key) => {
                let value = self.values.next().expect("Internal error: invalid size for values iterator");
                Some((key, value))
            }
            None => {
                debug_assert!(self.values.next().is_none());
                None
            }
        }
    }
}


// Traits: Extend, FromIterator
