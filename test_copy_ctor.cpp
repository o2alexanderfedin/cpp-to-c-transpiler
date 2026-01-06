struct Matrix3x3 {
    float data[9];
    Matrix3x3() {}
    Matrix3x3(const Matrix3x3& other) {
        for (int i = 0; i < 9; i++) data[i] = other.data[i];
    }
    
    Matrix3x3 add(const Matrix3x3& other) const {
        Matrix3x3 result;
        for (int i = 0; i < 9; i++) {
            result.data[i] = data[i] + other.data[i];
        }
        return result;
    }
};
