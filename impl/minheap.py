class MinHeap:
    def __init__(self):
        # 初始化
        self.heap_list = [0]
        self.current_size = 0

    def insert(self, k):
        # 将k放入最小堆中，同时维护最小堆
        if len(self.heap_list) - 1 == self.current_size:
            self.heap_list.append(k)
        else:
            self.heap_list[self.current_size + 1] = k
        self.sift_up(self.current_size + 1)
        self.current_size += 1

    def sift_up(self, i):
        # 向上移动二叉树中的值，维护最小堆
        while i // 2 > 0:
            if self.heap_list[i] < self.heap_list[i // 2]:
                self.heap_list[i], self.heap_list[i // 2] = self.heap_list[i // 2], self.heap_list[i]
            i = i // 2

    def sift_down(self, i):
        # 向下移动二叉树中的值，维护最小堆
        while (i * 2) <= self.current_size:
            mc = self.min_child(i)
            if self.heap_list[i] > self.heap_list[mc]:
                self.heap_list[i], self.heap_list[mc] = self.heap_list[mc], self.heap_list[i]
            i = mc

    def min_child(self, i):
        if (i * 2) + 1 > self.current_size:
            return i * 2
        else:
            if self.heap_list[i * 2] < self.heap_list[(i * 2) + 1]:
                return i * 2
            else:
                return (i * 2) + 1

    def delete_min(self):
        # 删除最小值
        if len(self.heap_list) == 1:
            return 'Empty heap'

        root = self.heap_list[1]
        self.heap_list[1] = self.heap_list[self.current_size]
        *self.heap_list, _ = self.heap_list
        self.current_size -= 1

        self.sift_down(1)
        return root
    
    def sort(self):
        new_arr = self.heap_list[1:]
        new_arr.sort()
        return new_arr
    
    def empty(self):
        return len(self.heap_list)==0

    def __iter__(self):
        return self
    
    def __next__(self):
        if len(self.heap_list) == 1:
            raise StopIteration
        return self.delete_min()