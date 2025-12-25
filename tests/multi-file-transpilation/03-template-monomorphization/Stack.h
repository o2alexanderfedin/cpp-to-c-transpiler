#ifndef STACK_H
#define STACK_H

template<typename T>
class Stack {
public:
  Stack() : m_size(0), m_capacity(10) {
    m_data = new T[m_capacity];
  }

  ~Stack() {
    delete[] m_data;
  }

  void push(T value) {
    if (m_size >= m_capacity) {
      resize();
    }
    m_data[m_size++] = value;
  }

  T pop() {
    return m_data[--m_size];
  }

  bool empty() const {
    return m_size == 0;
  }

private:
  void resize() {
    m_capacity *= 2;
    T* newData = new T[m_capacity];
    for (int i = 0; i < m_size; ++i) {
      newData[i] = m_data[i];
    }
    delete[] m_data;
    m_data = newData;
  }

  T* m_data;
  int m_size;
  int m_capacity;
};

#endif // STACK_H
