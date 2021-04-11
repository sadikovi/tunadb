// #[derive(Clone, Copy, Debug, PartialEq)]
// enum PageType {
//   Internal,
//   Leaf,
// }
//
// struct Page {
//   pub page_type: PageType,
//   pub page_id: u32,
//   pub keys: Vec<i32>,
//   pub values: Vec<i32>,
//   pub pages: Vec<u32>,
// }
//
// trait BufferPool {
//   // Creates a new page and returns page id.
//   fn create_new_page(&mut self, page_size: usize, page_type: PageType) -> u32;
//   // Returns a reference to the page.
//   fn get_page(&self, page_id: u32) -> &Page;
//   // Returns a copy of the page for modifications
//   fn get_page_mut(&self, page_id: u32) -> Page;
//   // Saves the resulting page in the buffer pool
//   fn set_page(&mut self, page: Page);
// }
//
// struct BTree<'a> {
//   page_size: usize,
//   max_values: usize,
//   buffer_pool: &'a mut BufferPool,
//   root: u32, // root page id
// }
//
// impl<'a> BTree<'a> {
//   pub fn create(buffer_pool: &'a mut BufferPool, page_size: usize, max_values: usize) -> Self {
//     let page_id = buffer_pool.create_new_page(page_size, PageType::Leaf);
//     Self { page_size: page_size, max_values: max_values, buffer_pool: buffer_pool, root: page_id }
//   }
//
//   pub fn insert(&mut self, key: i32, value: i32) {
//     let mut curr = self.root;
//     let mut parent_stack: Vec<(u32, usize)> = Vec::new();
//
//     loop {
//       let page = self.buffer_pool.get_page(curr);
//       if page.page_type == PageType::Leaf {
//         break;
//       }
//       // Find the page to traverse
//       let (i, next_page_id) = Self::search_pointer(page, key);
//       parent_stack.push((curr, i));
//       curr = next_page_id;
//     }
//
//     // Now curr points to a leaf page, find where to insert values
//     let mut page_mut = self.buffer_pool.get_page_mut(curr);
//     Self::page_insert(&mut page_mut, key, value);
//
//     // Perform split
//     if let Some((separator, page_mut_2)) = self.split(&mut page_mut) {
//       self.buffer_pool.set_page(page_mut_2);
//       self.split_internal_pages(parent_stack, separator);
//     }
//
//     self.buffer_pool.set_page(page_mut);
//   }
//
//   fn search_pointer(page: &Page, key: i32) -> (usize, u32) {
//     unimplemented!();
//   }
//
//   fn page_insert(page: &mut Page, key: i32, value: i32) {
//     unimplemented!();
//   }
//
//   fn split(&mut self, page: &mut Page) -> Option<(i32, Page)> {
//     unimplemented!();
//   }
// }
