package com.product.api.service;

import java.util.List;

import org.springframework.stereotype.Service;

import com.product.api.dto.ApiResponse;
import com.product.api.entity.Category;

@Service
public interface SvcCategory {
    
    List<Category> getCategories();
    Category getCategory(Integer category_id);
    ApiResponse createCategory(Category category);
    ApiResponse updateCategory(Integer category_id, Category category);
    ApiResponse deleteCategory(Integer category_id);
}
