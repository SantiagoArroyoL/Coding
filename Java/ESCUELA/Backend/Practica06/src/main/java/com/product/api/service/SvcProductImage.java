package com.product.api.service;

import java.util.List;

import com.product.api.dto.ApiResponse;
import com.product.api.entity.ProductImage;

public interface SvcProductImage {
    ApiResponse setProductImage(ProductImage in);

    List<ProductImage> getProductImages(Integer product_id);

    ApiResponse createProductImage(ProductImage in);

    ApiResponse deleteProductImage(Integer id);
}
