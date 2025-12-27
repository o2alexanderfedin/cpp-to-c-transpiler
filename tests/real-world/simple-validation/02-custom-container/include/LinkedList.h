#ifndef LINKEDLIST_H
#define LINKEDLIST_H

#include <cstddef>

template<typename T>
class LinkedList {
private:
    struct Node {
        T data;
        Node* next;

        Node(const T& value) : data(value), next(nullptr) {}
    };

    Node* head;
    Node* tail;
    size_t count;

public:
    LinkedList();
    ~LinkedList();

    void push_back(const T& value);
    void push_front(const T& value);
    void pop_front();
    T front() const;
    size_t size() const;
    bool isEmpty() const;
    void clear();
};

// Template implementation
template<typename T>
LinkedList<T>::LinkedList() : head(nullptr), tail(nullptr), count(0) {}

template<typename T>
LinkedList<T>::~LinkedList() {
    clear();
}

template<typename T>
void LinkedList<T>::push_back(const T& value) {
    Node* newNode = new Node(value);
    if (tail == nullptr) {
        head = tail = newNode;
    } else {
        tail->next = newNode;
        tail = newNode;
    }
    count++;
}

template<typename T>
void LinkedList<T>::push_front(const T& value) {
    Node* newNode = new Node(value);
    newNode->next = head;
    head = newNode;
    if (tail == nullptr) {
        tail = head;
    }
    count++;
}

template<typename T>
void LinkedList<T>::pop_front() {
    if (head != nullptr) {
        Node* temp = head;
        head = head->next;
        if (head == nullptr) {
            tail = nullptr;
        }
        delete temp;
        count--;
    }
}

template<typename T>
T LinkedList<T>::front() const {
    return head->data;
}

template<typename T>
size_t LinkedList<T>::size() const {
    return count;
}

template<typename T>
bool LinkedList<T>::isEmpty() const {
    return count == 0;
}

template<typename T>
void LinkedList<T>::clear() {
    while (head != nullptr) {
        Node* temp = head;
        head = head->next;
        delete temp;
    }
    tail = nullptr;
    count = 0;
}

#endif // LINKEDLIST_H
