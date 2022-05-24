package com.product.api.service;

import java.util.List;

import org.springframework.stereotype.Service;

import com.product.api.dto.ApiResponse;
import com.product.api.entity.Category;
import com.product.api.entity.Product;

@Service
public interface SvcProduct {

    List<Product> getProducts(Integer category_id);

    Product getProduct(String gtin);

    ApiResponse createProduct(Product in);

    ApiResponse updateProduct(Product in, Integer id);

    ApiResponse deleteProduct(Integer id);

    ApiResponse updateProductCategory(Category in, Integer id);
}
