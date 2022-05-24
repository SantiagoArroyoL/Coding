package com.product.api.service;

import java.util.List;

import com.product.api.dto.ApiResponse;
import com.product.api.entity.Category;
import com.product.api.entity.Product;
import com.product.api.repository.RepoCategory;
import com.product.api.repository.RepoProduct;
import com.product.exception.ApiException;

import org.hibernate.exception.ConstraintViolationException;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.dao.DataIntegrityViolationException;
import org.springframework.http.HttpStatus;
import org.springframework.stereotype.Service;

@Service
public class SvcProductImp implements SvcProduct {

    @Autowired
    RepoProduct repo;

    @Autowired
    RepoCategory repoCategory;

    @Override
    public List<Product> getProducts(Integer category_id) {
        return repo.findByStatus(1);
    }

    @Override
    public Product getProduct(String gtin) {
        Product product = repo.findByGtinAndStatus(gtin, 1);
        if (product != null) {
            product.setCategory(repoCategory.findByCategoryId(product.getCategory_id()));
            return product;
        } else
            throw new ApiException(HttpStatus.NOT_FOUND, "product does not exist");
    }

    @Override
    public ApiResponse createProduct(Product in) {
        Product product = repo.findByGtinAndStatus(in.getGtin(), 0);
        if (product != null) {
            updateProduct(in, product.getProduct_id());
            return new ApiResponse("product activated");
        } else {
            try {
                in.setStatus(1);
                repo.save(in);
            } catch (ConstraintViolationException e) {
                if (e.getLocalizedMessage().contains("gtin"))
                    throw new ApiException(HttpStatus.BAD_REQUEST, "product gtin already exists");
                if (e.getLocalizedMessage().contains("name"))
                    throw new ApiException(HttpStatus.BAD_REQUEST, "product name already exists");
            }
        }
        return new ApiResponse("product created");
    }

    @Override
    public ApiResponse updateProduct(Product in, Integer id) {
        try {
            repo.updateProduct(id, in.getGtin(),
                    in.getProduct(),
                    in.getDescription(),
                    in.getPrice(),
                    in.getStock());
        } catch (DataIntegrityViolationException e) {
            if (e.getLocalizedMessage().contains("gtin"))
                throw new ApiException(HttpStatus.BAD_REQUEST, "product gtin already exists");
            if (e.getLocalizedMessage().contains("name"))
                throw new ApiException(HttpStatus.BAD_REQUEST, "product name already exists");
        }
        return new ApiResponse("product updated");
    }

    @Override
    public ApiResponse deleteProduct(Integer id) {
        if (repo.deleteProduct(id) > 0)
            return new ApiResponse("product deleted");
        else
            throw new ApiException(HttpStatus.BAD_REQUEST, "product cannot be deleted");
    }

    @Override
    public ApiResponse updateProductCategory(Category in, Integer id) {
        try {
            if (repo.updateProductCategory(in.getCategory_id(), id) > 0)
                return new ApiResponse("product category updated");
            else
                throw new ApiException(HttpStatus.BAD_REQUEST, "product category cannot be updated");
        } catch (DataIntegrityViolationException e) {
            throw new ApiException(HttpStatus.NOT_FOUND, "category not found");
        }
    }

}
