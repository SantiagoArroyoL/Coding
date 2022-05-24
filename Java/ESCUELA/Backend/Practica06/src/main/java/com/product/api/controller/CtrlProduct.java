package com.product.api.controller;

import javax.validation.Valid;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.http.HttpStatus;
import org.springframework.http.ResponseEntity;
import org.springframework.validation.BindingResult;
import org.springframework.web.bind.annotation.DeleteMapping;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.PathVariable;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.PutMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;

import com.product.api.dto.ApiResponse;
import com.product.api.entity.Category;
import com.product.api.entity.Product;
import com.product.api.service.SvcProduct;
import com.product.exception.ApiException;

@RestController
@RequestMapping("/product")
public class CtrlProduct {

    @Autowired
    SvcProduct svc;

    @GetMapping("/{gtin}")
    public ResponseEntity<Product> readProduct(@PathVariable("gtin") String gtin) {
        return new ResponseEntity<>(svc.getProduct(gtin), HttpStatus.OK);
    }

    @PostMapping
    public ResponseEntity<ApiResponse> createProduct(@Valid @RequestBody Product in,
            BindingResult bindingResult) {
        if (bindingResult.hasErrors()) {
            throw new ApiException(HttpStatus.BAD_REQUEST, bindingResult.getAllErrors().get(0).getDefaultMessage());
        }
        return new ResponseEntity<>(svc.createProduct(in), HttpStatus.OK);
    }

    @PutMapping("/{id}")
    public ResponseEntity<ApiResponse> updateProduct(@PathVariable("id") int id,
            @Valid @RequestBody Product in, BindingResult bindingResult) {
        if (bindingResult.hasErrors()) {
            throw new ApiException(HttpStatus.BAD_REQUEST, bindingResult.getAllErrors().get(0).getDefaultMessage());
        }
        return new ResponseEntity<>(svc.updateProduct(in, id), HttpStatus.OK);
    }

    @DeleteMapping("/{id}")
    public ResponseEntity<ApiResponse> deleteProduct(@PathVariable("id") int id) {
        return new ResponseEntity<>(svc.deleteProduct(id), HttpStatus.OK);
    }

    @PutMapping("/{id}/category")
    public ResponseEntity<ApiResponse> updateProductCategory(@PathVariable("id") int id,
            @Valid @RequestBody Category in, BindingResult bindingResult) {
        if (bindingResult.hasErrors()) {
            throw new ApiException(HttpStatus.BAD_REQUEST, bindingResult.getAllErrors().get(0).getDefaultMessage());
        }
        return new ResponseEntity<>(svc.updateProductCategory(in, id), HttpStatus.OK);
    }
}
